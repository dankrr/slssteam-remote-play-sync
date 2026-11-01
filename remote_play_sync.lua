-- SLSsteam Bidirectional Remote Library Synchronization Plugin (remote_play_sync.lua)
--
-- Single-file portable LuaJIT plugin supporting:
--   1. Tier 1 ("managed-owner"): Full background synchronization when maintained
--      SLSsteam exposes SLS.onTick, SLS.onShutdown, SLS.cancelCallback,
--      SLS.Transport, and SLS.RuntimeApps.
--   2. Tier 2 ("stock-opportunistic"): Safe, honest working subset on unmodified
--      stock 32-bit and 64-bit SLSsteam builds (deferred until SLSsteam::initialized,
--      driven opportunistically by configLoaded/initialized/Network::recvPkt/sendPkt,
--      preserving legitimate Steam entitlements via CUser:isSubscribed).
--   3. Standalone CLI mode ("luajit remote_play_sync.lua --init-pair / --validate-config"):
--      Generates owner-only (0600) paired configuration files using Linux getrandom()
--      and validates permissions/schema via fixed-width Linux statx ABI.
--
-- Zero dlopen/dlmopen calls: FIPS 180-4 SHA-256 and RFC 2104 HMAC-SHA-256 are
-- implemented directly in LuaJIT (bit + FFI) to avoid glibc _dl_load_lock and
-- LD_AUDIT namespace allocator hazards across 32-bit and 64-bit Steam processes.

local okBit, bit = pcall(require, "bit")
local okFfi, ffi = pcall(require, "ffi")
local ENV = (getfenv and getfenv(1)) or _G

local MAX_SAFE_INTEGER = 9007199254740991
local MAX_RETIRED_SESSIONS = 16
local MAX_TOMBSTONES = 4096
local MAX_APPS = 65536
local MAX_SNAPSHOT = 2 * 1024 * 1024
local CHUNK_DATA = 60000
local MAX_CHUNKS = 35
local MAX_FRAME = 128 * 1024
local MAX_READ_BUFFER = 2 * MAX_FRAME
local MAX_WRITE_BYTES = 1024 * 1024
local MAX_CONFIG_BYTES = 16384
local CHANNEL = "sls.remote-play-sync.v1"
local ADAPTER_NAME = "lua-direct-tcp-hmac-v1"
local HEARTBEAT_CHANNEL = "sls.heartbeat.v1"
local PROTOCOL_MAGIC = "SLSRPS" .. string.char(3, 1)

-- ============================================================================
-- Pure-LuaJIT FIPS 180-4 SHA-256 & RFC 2104 HMAC-SHA-256 (Zero dlopen/libcrypto)
-- ============================================================================

local SHA256_K = okBit and {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
} or nil

if SHA256_K then
    for i = 1, 64 do
        SHA256_K[i] = bit.tobit(SHA256_K[i])
    end
end

local sha256Schedule = (okFfi and okBit) and ffi.new("int32_t[64]") or nil

local function u16be(value)
    return string.char(
        bit.band(bit.rshift(value, 8), 0xff),
        bit.band(value, 0xff)
    )
end

local function u32be(value)
    return string.char(
        bit.band(bit.rshift(value, 24), 0xff),
        bit.band(bit.rshift(value, 16), 0xff),
        bit.band(bit.rshift(value, 8), 0xff),
        bit.band(value, 0xff)
    )
end

local function sha256(message)
    if not okBit or type(message) ~= "string" then return nil end
    local band, bor, bxor, bnot = bit.band, bit.bor, bit.bxor, bit.bnot
    local lshift, rshift, ror, tobit = bit.lshift, bit.rshift, bit.ror, bit.tobit

    local len = #message
    local bitLenHi = math.floor(len / 536870912)
    local bitLenLo = tobit((len % 536870912) * 8)
    local padZeroCount = (56 - ((len + 1) % 64)) % 64
    local padded = message .. "\128" .. string.rep("\0", padZeroCount)
        .. u32be(bitLenHi) .. u32be(bitLenLo)

    local h0 = tobit(0x6a09e667)
    local h1 = tobit(0xbb67ae85)
    local h2 = tobit(0x3c6ef372)
    local h3 = tobit(0xa54ff53a)
    local h4 = tobit(0x510e527f)
    local h5 = tobit(0x9b05688c)
    local h6 = tobit(0x1f83d9ab)
    local h7 = tobit(0x5be0cd19)

    local w = sha256Schedule or {}
    local k = SHA256_K

    for chunkStart = 1, #padded, 64 do
        for i = 0, 15 do
            local pos = chunkStart + i * 4
            local b0, b1, b2, b3 = padded:byte(pos, pos + 3)
            w[i] = bor(lshift(b0, 24), lshift(b1, 16), lshift(b2, 8), b3)
        end
        for i = 16, 63 do
            local w15 = w[i - 15]
            local s0 = bxor(ror(w15, 7), ror(w15, 18), rshift(w15, 3))
            local w2 = w[i - 2]
            local s1 = bxor(ror(w2, 17), ror(w2, 19), rshift(w2, 10))
            w[i] = tobit(w[i - 16] + s0 + w[i - 7] + s1)
        end

        local a, b, c, d, e, f, g, h = h0, h1, h2, h3, h4, h5, h6, h7
        for i = 0, 63 do
            local S1 = bxor(ror(e, 6), ror(e, 11), ror(e, 25))
            local ch = bxor(band(e, f), band(bnot(e), g))
            local temp1 = tobit(h + S1 + ch + k[i + 1] + w[i])
            local S0 = bxor(ror(a, 2), ror(a, 13), ror(a, 22))
            local maj = bxor(band(a, b), band(a, c), band(b, c))
            local temp2 = tobit(S0 + maj)

            h = g
            g = f
            f = e
            e = tobit(d + temp1)
            d = c
            c = b
            b = a
            a = tobit(temp1 + temp2)
        end

        h0 = tobit(h0 + a)
        h1 = tobit(h1 + b)
        h2 = tobit(h2 + c)
        h3 = tobit(h3 + d)
        h4 = tobit(h4 + e)
        h5 = tobit(h5 + f)
        h6 = tobit(h6 + g)
        h7 = tobit(h7 + h)
    end

    return u32be(h0) .. u32be(h1) .. u32be(h2) .. u32be(h3)
        .. u32be(h4) .. u32be(h5) .. u32be(h6) .. u32be(h7)
end

local function hmacSha256(key, message)
    if not okBit or type(key) ~= "string" or type(message) ~= "string" then
        return nil
    end
    if #key > 64 then
        key = sha256(key)
        if not key then return nil end
    end
    if #key < 64 then
        key = key .. string.rep("\0", 64 - #key)
    end
    local ipadBytes, opadBytes = {}, {}
    for i = 1, 64 do
        local kb = key:byte(i)
        ipadBytes[i] = string.char(bit.bxor(kb, 0x36))
        opadBytes[i] = string.char(bit.bxor(kb, 0x5c))
    end
    local inner = sha256(table.concat(ipadBytes) .. message)
    if not inner then return nil end
    return sha256(table.concat(opadBytes) .. inner)
end

local function secureEqual(left, right)
    if not okBit or type(left) ~= "string" or type(right) ~= "string" or #left ~= #right then
        return false
    end
    local difference = 0
    for index = 1, #left do
        difference = bit.bor(difference, bit.bxor(left:byte(index), right:byte(index)))
    end
    return difference == 0
end

local function fromHex(text)
    if type(text) ~= "string" or (#text % 2) ~= 0 or not text:match("^[0-9a-fA-F]*$") then
        return nil
    end
    local bytes = {}
    for index = 1, #text, 2 do
        bytes[#bytes + 1] = string.char(tonumber(text:sub(index, index + 1), 16))
    end
    return table.concat(bytes)
end

local function toHex(text)
    if type(text) ~= "string" then return nil end
    return (text:gsub(".", function(byte)
        return string.format("%02x", byte:byte())
    end))
end

-- ============================================================================
-- Linux FFI Declarations (32-bit x86 & 64-bit x86-64 ABI-safe, reload-safe)
-- ============================================================================

local function ensureLinuxFfi()
    if not okFfi or not okBit or ffi.os ~= "Linux" then
        return false
    end
    if not rawget(_G, "__SLS_RPS_FFI_V3") then
        ffi.cdef[[
struct sls_rps_in_addr { uint32_t s_addr; };
struct sls_rps_sockaddr { uint16_t sa_family; char sa_data[14]; };
struct sls_rps_sockaddr_in {
    uint16_t sin_family;
    uint16_t sin_port;
    struct sls_rps_in_addr sin_addr;
    uint8_t sin_zero[8];
};
struct sls_rps_pollfd { int32_t fd; int16_t events; int16_t revents; };
struct sls_rps_timespec { long tv_sec; long tv_nsec; };
struct sls_rps_statx {
    uint32_t stx_mask;
    uint32_t stx_blksize;
    uint64_t stx_attributes;
    uint32_t stx_nlink;
    uint32_t stx_uid;
    uint32_t stx_gid;
    uint16_t stx_mode;
    uint16_t __spare0[1];
    uint64_t stx_ino;
    uint64_t stx_size;
    uint64_t stx_blocks;
    uint64_t stx_attributes_mask;
    uint8_t  __tail[192];
};

int socket(int domain, int type, int protocol);
int bind(int fd, const struct sls_rps_sockaddr *address, uint32_t length);
int listen(int fd, int backlog);
int accept4(int fd, struct sls_rps_sockaddr *address, uint32_t *length, int flags);
int connect(int fd, const struct sls_rps_sockaddr *address, uint32_t length);
int getsockopt(int fd, int level, int option, void *value, uint32_t *length);
int setsockopt(int fd, int level, int option, const void *value, uint32_t length);
int inet_pton(int family, const char *text, void *output);
ssize_t send(int fd, const void *buffer, size_t length, int flags);
ssize_t recv(int fd, void *buffer, size_t length, int flags);
int poll(struct sls_rps_pollfd *descriptors, unsigned long count, int timeout_ms);
int open(const char *pathname, int flags, ...);
ssize_t read(int fd, void *buffer, size_t count);
ssize_t write(int fd, const void *buffer, size_t count);
int fchmod(int fd, uint32_t mode);
int close(int fd);
int statx(int dirfd, const char *pathname, int flags, unsigned int mask, struct sls_rps_statx *statxbuf);
uint32_t geteuid(void);
ssize_t getrandom(void *buffer, size_t length, unsigned int flags);
int clock_gettime(int clock_id, struct sls_rps_timespec *time);
int gettid(void);
]]
        rawset(_G, "__SLS_RPS_FFI_V3", true)
    end
    return true
end

local AF_INET, SOCK_STREAM = 2, 1
local SOCK_NONBLOCK, SOCK_CLOEXEC = 0x800, 0x80000
local SOL_SOCKET, SO_REUSEADDR, SO_ERROR, SO_SNDBUF = 1, 2, 4, 7
local POLLIN, POLLOUT = 1, 4
local POLLERR, POLLHUP, POLLNVAL, POLLRDHUP = 0x8, 0x10, 0x20, 0x2000
local MSG_NOSIGNAL = 0x4000
local EAGAIN, EINTR, ENOENT, EINPROGRESS = 11, 4, 2, 115
local O_RDONLY, O_WRONLY, O_CREAT, O_TRUNC = 0, 1, 0x40, 0x200
local O_NOFOLLOW, O_CLOEXEC = 0x20000, 0x80000
local AT_EMPTY_PATH = 0x1000
local STATX_TYPE, STATX_MODE, STATX_UID, STATX_SIZE = 0x1, 0x2, 0x8, 0x200
local S_IFMT, S_IFREG = 0xf000, 0x8000
local CLOCK_MONOTONIC, CLOCK_BOOTTIME = 1, 7
local GRND_NONBLOCK = 1

local function closeFd(fd)
    if fd and fd >= 0 then ffi.C.close(fd) end
end

local function randomBytes(count)
    if not ensureLinuxFfi() or type(count) ~= "number" or count < 1 then return nil end
    local output = ffi.new("uint8_t[?]", count)
    local offset = 0
    while offset < count do
        local rc = tonumber(ffi.C.getrandom(output + offset, count - offset, GRND_NONBLOCK))
        if rc and rc > 0 then
            offset = offset + rc
        elseif not rc or ffi.errno() ~= EINTR then
            return nil
        end
    end
    return ffi.string(output, count)
end

local function nowMs()
    if not ensureLinuxFfi() then return 0 end
    local value = ffi.new("struct sls_rps_timespec[2]")
    if ffi.C.clock_gettime(CLOCK_BOOTTIME, value) ~= 0 then
        if ffi.C.clock_gettime(CLOCK_MONOTONIC, value) ~= 0 then return 0 end
    end
    return tonumber(value[0].tv_sec) * 1000 + math.floor(tonumber(value[0].tv_nsec) / 1000000)
end

-- ============================================================================
-- Network Policy, Config File Parser, Owner-Only Permission Check, Pairing CLI
-- ============================================================================

local function isAllowedPrivateIPv4(address)
    if type(address) ~= "string" then return false end
    local a, b, c, d = address:match("^(%d+)%.(%d+)%.(%d+)%.(%d+)$")
    if not a then return false end
    for _, part in ipairs({ a, b, c, d }) do
        if #part > 1 and part:sub(1, 1) == "0" then return false end
    end
    a, b, c, d = tonumber(a), tonumber(b), tonumber(c), tonumber(d)
    if not a or a > 255 or b > 255 or c > 255 or d > 255 then return false end
    -- Loopback 127.0.0.0/8 (local/isolated testing)
    if a == 127 then return true end
    -- Tailscale CGNAT 100.64.0.0/10
    if a == 100 and b >= 64 and b <= 127 then return true end
    -- RFC 1918 private LAN ranges: 10.0.0.0/8, 172.16.0.0/12, 192.168.0.0/16
    if a == 10 then return true end
    if a == 172 and b >= 16 and b <= 31 then return true end
    if a == 192 and b == 168 then return true end
    return false
end

local function defaultConfigPath()
    local explicit = os.getenv("SLS_RPS_CONFIG")
    if explicit and explicit ~= "" then return explicit, true end
    local xdg = os.getenv("XDG_CONFIG_HOME")
    if xdg and xdg ~= "" then
        return xdg .. "/SLSsteam/remote_play_sync.conf", false
    end
    local home = os.getenv("HOME")
    if home and home ~= "" then
        return home .. "/.config/SLSsteam/remote_play_sync.conf", false
    end
    return nil, false
end

local function parseConfigText(text)
    if type(text) ~= "string" or #text > MAX_CONFIG_BYTES then
        return nil, "config-oversize"
    end
    local values = {}
    local lineNumber = 0
    for rawLine in (text .. "\n"):gmatch("([^\n]*)\n") do
        lineNumber = lineNumber + 1
        local line = rawLine:gsub("\r$", "")
        if line:find("[%z\1-\8\11\12\14-\31]") then
            return nil, "config-control-char"
        end
        local trimmed = line:match("^%s*(.-)%s*$")
        if trimmed ~= "" and trimmed:sub(1, 1) ~= "#" then
            local key, val = trimmed:match("^([A-Z0-9_]+)%s*=%s*(.-)%s*$")
            if not key then
                return nil, "config-syntax-line-" .. tostring(lineNumber)
            end
            if #val >= 2 and ((val:sub(1, 1) == '"' and val:sub(-1) == '"')
                or (val:sub(1, 1) == "'" and val:sub(-1) == "'")) then
                val = val:sub(2, -2)
            end
            values[key] = val
        end
    end
    return values
end

local function loadConfigFile(path, required)
    if not path or path == "" then
        if required then return nil, "missing-config-path" end
        return {}
    end
    if not ensureLinuxFfi() then return nil, "ffi-unavailable" end
    local fd = ffi.C.open(path, bit.bor(O_RDONLY, O_NOFOLLOW, O_CLOEXEC), ffi.cast("unsigned int", 0))
    if fd < 0 then
        local err = ffi.errno()
        if err == ENOENT and not required then
            return {}
        end
        return nil, err == ENOENT and "config-not-found" or "config-open-failed"
    end
    local stx = ffi.new("struct sls_rps_statx[1]")
    local mask = bit.bor(STATX_TYPE, STATX_MODE, STATX_UID, STATX_SIZE)
    if ffi.C.statx(fd, "", AT_EMPTY_PATH, mask, stx) ~= 0
        or bit.band(stx[0].stx_mask, mask) ~= mask then
        closeFd(fd)
        return nil, "config-statx-failed"
    end
    local mode = tonumber(stx[0].stx_mode)
    if bit.band(mode, S_IFMT) ~= S_IFREG then
        closeFd(fd)
        return nil, "config-not-regular-file"
    end
    if tonumber(stx[0].stx_uid) ~= tonumber(ffi.C.geteuid()) then
        closeFd(fd)
        return nil, "config-uid-mismatch"
    end
    if bit.band(mode, 0x3f) ~= 0 then
        closeFd(fd)
        return nil, "insecure-config-permissions"
    end
    local size = tonumber(stx[0].stx_size)
    if not size or size < 0 or size > MAX_CONFIG_BYTES then
        closeFd(fd)
        return nil, "config-oversize"
    end
    local buf = ffi.new("uint8_t[?]", MAX_CONFIG_BYTES + 1)
    local chunks, total = {}, 0
    while true do
        local rc = tonumber(ffi.C.read(fd, buf, MAX_CONFIG_BYTES + 1 - total))
        if rc and rc > 0 then
            total = total + rc
            if total > MAX_CONFIG_BYTES then
                closeFd(fd)
                return nil, "config-oversize"
            end
            chunks[#chunks + 1] = ffi.string(buf, rc)
        elseif rc == 0 then
            break
        elseif not rc or ffi.errno() ~= EINTR then
            closeFd(fd)
            return nil, "config-read-failed"
        end
    end
    closeFd(fd)
    return parseConfigText(table.concat(chunks))
end

local function resolveSettings(explicitConfigPath)
    local memConfig = ENV.REMOTE_PLAY_SYNC_CONFIG
    local cfgPath, cfgExplicit
    if explicitConfigPath ~= nil then
        cfgPath, cfgExplicit = explicitConfigPath, true
    else
        cfgPath, cfgExplicit = defaultConfigPath()
    end
    local fileConfig, fileErr = {}, nil
    if type(memConfig) ~= "table" or cfgExplicit then
        fileConfig, fileErr = loadConfigFile(cfgPath, cfgExplicit)
        if not fileConfig then return nil, fileErr end
    end
    memConfig = type(memConfig) == "table" and memConfig or {}

    local function setting(name, default)
        local value = memConfig[name]
        if value == nil or value == "" then
            value = os.getenv("SLS_RPS_" .. name)
        end
        if value == nil or value == "" then
            value = fileConfig[name]
        end
        if value == nil or value == "" then return default end
        return tostring(value)
    end

    local mode = setting("MODE")
    if mode ~= "listen" and mode ~= "connect" and mode ~= "auto" then
        return nil, "invalid-mode"
    end
    local deviceId = setting("DEVICE_ID")
    local peerId = setting("PEER_ID")
    local pskHex = setting("PSK_HEX")
    if type(deviceId) ~= "string" or #deviceId ~= 32 or not deviceId:match("^[0-9a-fA-F]+$") then
        return nil, "invalid-device-id"
    end
    if type(peerId) ~= "string" or #peerId ~= 32 or not peerId:match("^[0-9a-fA-F]+$")
        or peerId:lower() == deviceId:lower() then
        return nil, "invalid-peer-id"
    end
    if type(pskHex) ~= "string" or #pskHex ~= 64 or not pskHex:match("^[0-9a-fA-F]+$") then
        return nil, "invalid-psk"
    end

    local defaultPort = tonumber(setting("PORT"))
    local bindHost, bindPort, peerHost, peerPort
    if mode == "listen" then
        bindHost = setting("BIND_HOST", setting("HOST"))
        bindPort = tonumber(setting("BIND_PORT", defaultPort and tostring(defaultPort) or nil))
        if not bindHost or not bindPort or bindPort < 1 or bindPort > 65535
            or bindPort ~= math.floor(bindPort) then
            return nil, "invalid-address"
        end
        if not isAllowedPrivateIPv4(bindHost) then return nil, "non-private-address" end
    elseif mode == "connect" then
        peerHost = setting("PEER_HOST", setting("HOST"))
        peerPort = tonumber(setting("PEER_PORT", defaultPort and tostring(defaultPort) or nil))
        if not peerHost or not peerPort or peerPort < 1 or peerPort > 65535
            or peerPort ~= math.floor(peerPort) then
            return nil, "invalid-address"
        end
        if not isAllowedPrivateIPv4(peerHost) then return nil, "non-private-address" end
    else -- mode == "auto"
        bindHost = setting("BIND_HOST")
        peerHost = setting("PEER_HOST")
        bindPort = tonumber(setting("BIND_PORT", defaultPort and tostring(defaultPort) or nil))
        peerPort = tonumber(setting("PEER_PORT", defaultPort and tostring(defaultPort) or nil))
        if not bindHost or not peerHost or not bindPort or not peerPort
            or bindPort < 1 or bindPort > 65535 or bindPort ~= math.floor(bindPort)
            or peerPort < 1 or peerPort > 65535 or peerPort ~= math.floor(peerPort) then
            return nil, "invalid-address"
        end
        if not isAllowedPrivateIPv4(bindHost) or not isAllowedPrivateIPv4(peerHost) then
            return nil, "non-private-address"
        end
    end

    local tickMs = tonumber(setting("TICK_MS", "10"))
    if not tickMs or tickMs < 1 or tickMs > 1000 or tickMs ~= math.floor(tickMs) then
        return nil, "invalid-tick"
    end

    local hasMemTable = type(ENV.REMOTE_PLAY_SYNC_CONFIG) == "table"
    local explicitSteamRoot = setting("STEAM_ROOT")
    local explicitSyncInstalled = setting("SYNC_INSTALLED")
    local defaultSyncInstalled = "1"
    if (hasMemTable or ENV.TEST_STEAM_ID ~= nil)
        and not explicitSteamRoot and not explicitSyncInstalled then
        defaultSyncInstalled = "0"
    end
    local syncInstalled = (explicitSyncInstalled or defaultSyncInstalled) ~= "0"
    local steamRoot = explicitSteamRoot or ((os.getenv("HOME") or "") .. "/.local/share/Steam")

    return {
        mode = mode,
        deviceId = deviceId:lower(),
        peerId = peerId:lower(),
        psk = fromHex(pskHex),
        bindHost = bindHost,
        bindPort = bindPort,
        peerHost = peerHost,
        peerPort = peerPort,
        tickMs = tickMs,
        syncInstalled = syncInstalled,
        steamRoot = steamRoot,
    }
end

local function writeSecureFile(path, content)
    if not ensureLinuxFfi() then return false, "ffi-unavailable" end
    local flags = bit.bor(O_WRONLY, O_CREAT, O_TRUNC, O_NOFOLLOW, O_CLOEXEC)
    local fd = ffi.C.open(path, flags, ffi.cast("unsigned int", 0x180)) -- 0600
    if fd < 0 then return false, "open-failed" end
    if ffi.C.fchmod(fd, 0x180) ~= 0 then
        closeFd(fd)
        return false, "fchmod-failed"
    end
    local ptr = ffi.cast("const uint8_t*", content)
    local offset = 0
    while offset < #content do
        local rc = tonumber(ffi.C.write(fd, ptr + offset, #content - offset))
        if rc and rc > 0 then
            offset = offset + rc
        elseif not rc or ffi.errno() ~= EINTR then
            closeFd(fd)
            return false, "write-failed"
        end
    end
    closeFd(fd)
    return true
end

local function writePairConfigs(opts)
    if type(opts) ~= "table" then return false, "invalid-options" end
    local mode = opts.mode or "auto"
    local portA = tonumber(opts.portA or opts.port or 47999)
    local portB = tonumber(opts.portB or opts.port or 47999)
    if (mode ~= "auto" and mode ~= "listen-connect")
        or not isAllowedPrivateIPv4(opts.hostA) or not isAllowedPrivateIPv4(opts.hostB)
        or not portA or portA < 1 or portA > 65535 or portA ~= math.floor(portA)
        or not portB or portB < 1 or portB > 65535 or portB ~= math.floor(portB)
        or type(opts.outA) ~= "string" or opts.outA == ""
        or type(opts.outB) ~= "string" or opts.outB == "" then
        return false, "invalid-pair-parameters"
    end
    local idABytes = randomBytes(16)
    local idBBytes = randomBytes(16)
    local pskBytes = randomBytes(32)
    if not idABytes or not idBBytes or not pskBytes then return false, "random-unavailable" end
    local idA, idB, pskHex = toHex(idABytes), toHex(idBBytes), toHex(pskBytes)
    if idA == idB then return false, "device-id-collision" end

    local cfgA, cfgB
    if mode == "auto" then
        cfgA = table.concat({
            "# SLSsteam Remote Library Sync paired configuration (Device A) — keep mode 0600",
            "MODE=auto",
            "DEVICE_ID=" .. idA,
            "PEER_ID=" .. idB,
            "BIND_HOST=" .. opts.hostA,
            "BIND_PORT=" .. tostring(portA),
            "PEER_HOST=" .. opts.hostB,
            "PEER_PORT=" .. tostring(portB),
            "PSK_HEX=" .. pskHex,
            "TICK_MS=10",
            "",
        }, "\n")
        cfgB = table.concat({
            "# SLSsteam Remote Library Sync paired configuration (Device B) — keep mode 0600",
            "MODE=auto",
            "DEVICE_ID=" .. idB,
            "PEER_ID=" .. idA,
            "BIND_HOST=" .. opts.hostB,
            "BIND_PORT=" .. tostring(portB),
            "PEER_HOST=" .. opts.hostA,
            "PEER_PORT=" .. tostring(portA),
            "PSK_HEX=" .. pskHex,
            "TICK_MS=10",
            "",
        }, "\n")
    else
        cfgA = table.concat({
            "# SLSsteam Remote Library Sync paired configuration (Listener A) — keep mode 0600",
            "MODE=listen",
            "DEVICE_ID=" .. idA,
            "PEER_ID=" .. idB,
            "HOST=" .. opts.hostA,
            "PORT=" .. tostring(portA),
            "PSK_HEX=" .. pskHex,
            "TICK_MS=10",
            "",
        }, "\n")
        cfgB = table.concat({
            "# SLSsteam Remote Library Sync paired configuration (Connector B) — keep mode 0600",
            "MODE=connect",
            "DEVICE_ID=" .. idB,
            "PEER_ID=" .. idA,
            "HOST=" .. opts.hostA,
            "PORT=" .. tostring(portA),
            "PSK_HEX=" .. pskHex,
            "TICK_MS=10",
            "",
        }, "\n")
    end

    local okA, errA = writeSecureFile(opts.outA, cfgA)
    if not okA then return false, "write-a-" .. tostring(errA) end
    local okB, errB = writeSecureFile(opts.outB, cfgB)
    if not okB then return false, "write-b-" .. tostring(errB) end
    return true, { deviceA = idA, deviceB = idB }
end

-- Standalone CLI entry point when invoked directly with `luajit remote_play_sync.lua ...`
if ENV.SLS == nil and not ENV.REMOTE_PLAY_SYNC_TEST_MODE then
    local args = ENV.arg or {}
    local action = args[1]
    if action == "--init-pair" then
        local opts = {}
        local idx = 2
        while idx <= #args do
            local k, v = args[idx], args[idx + 1]
            if k == "--out-a" then opts.outA = v; idx = idx + 2
            elseif k == "--out-b" then opts.outB = v; idx = idx + 2
            elseif k == "--host-a" then opts.hostA = v; idx = idx + 2
            elseif k == "--host-b" then opts.hostB = v; idx = idx + 2
            elseif k == "--port" then opts.port = v; idx = idx + 2
            elseif k == "--port-a" then opts.portA = v; idx = idx + 2
            elseif k == "--port-b" then opts.portB = v; idx = idx + 2
            elseif k == "--mode" then opts.mode = v; idx = idx + 2
            else
                io.stderr:write("Unknown option: " .. tostring(k) .. "\n")
                os.exit(2)
            end
        end
        local ok, info = writePairConfigs(opts)
        if not ok then
            io.stderr:write("PAIR_INIT_FAILED: " .. tostring(info) .. "\n")
            os.exit(1)
        end
        io.stdout:write(string.format(
            "PAIR_INIT_OK device_a=%s device_b=%s (0600 files written; PSK not printed)\n",
            info.deviceA, info.deviceB
        ))
        os.exit(0)
    elseif action == "--validate-config" then
        local cfgPath = args[2] == "--config" and args[3] or args[2]
        local settings, err = resolveSettings(cfgPath)
        if not settings then
            io.stderr:write("CONFIG_INVALID: " .. tostring(err) .. "\n")
            os.exit(1)
        end
        io.stdout:write(string.format(
            "CONFIG_VALID mode=%s device=%s peer=%s\n",
            settings.mode, settings.deviceId, settings.peerId
        ))
        os.exit(0)
    else
        io.stdout:write(table.concat({
            "Usage:",
            "  luajit remote_play_sync.lua --init-pair --out-a <desktop.conf> --host-a <tailscale_ip_a> \\",
            "      --out-b <deck.conf> --host-b <tailscale_ip_b> [--port 47999] [--mode auto|listen-connect]",
            "  luajit remote_play_sync.lua --validate-config [--config <path/to/remote_play_sync.conf>]",
            "",
        }, "\n"))
        os.exit(action == "--help" and 0 or 2)
    end
end

-- ============================================================================
-- Plugin Runtime State & Helpers
-- ============================================================================

RemotePlaySync = RemotePlaySync or {}
local R = RemotePlaySync

-- Cleanly tear down any prior backend closure on stock SLSsteam hot-reload
-- (where Lua::init(false) re-runs plugins inside the same lua_State).
if type(R._stopActiveBackend) == "function" then
    pcall(R._stopActiveBackend, "hot-reload")
    R._stopActiveBackend = nil
end

local evidenceEnabled = os.getenv("SLS_RPS_EVIDENCE") == "1"
local function logInfo(msg) if log and log.info then log.info(msg) end end
local function logWarn(msg) if log and log.warn then log.warn(msg) end end
local function logDebug(msg) if log and log.debug then log.debug(msg) end end
local function evidence(message)
    if evidenceEnabled then logInfo("RemotePlaySync evidence " .. message) end
end
local function threadId()
    if ensureLinuxFfi() then return tonumber(ffi.C.gettid()) end
    return 0
end
local function evidenceIds(values)
    local parts = {}
    for index = 1, math.min(16, #values) do parts[index] = tostring(values[index]) end
    return table.concat(parts, ",")
end

local function validInteger(value)
    return type(value) == "number"
        and value >= 1
        and value <= MAX_SAFE_INTEGER
        and value == math.floor(value)
end

local function validNonNegativeInteger(value)
    return type(value) == "number"
        and value >= 0
        and value <= MAX_SAFE_INTEGER
        and value == math.floor(value)
end

local function normalizedSet(values)
    local result = {}
    if values == nil then return result end
    for _, value in pairs(values) do
        local appId = tonumber(value)
        if appId and validInteger(appId) and appId <= 0xffffffff then
            result[appId] = true
        end
    end
    return result
end

local function sortedList(values)
    local result = {}
    if not values then return result end
    for appId, present in pairs(values) do
        if present then result[#result + 1] = appId end
    end
    table.sort(result)
    return result
end

local function setKey(values)
    return table.concat(sortedList(values), ",")
end

local function sanitizeTitle(name)
    if type(name) ~= "string" or #name > 256 or name:find("[%z\1-\31]") then
        return nil
    end
    return name
end

local function readU16be(data, offset)
    if offset + 1 > #data then return nil end
    return data:byte(offset) * 256 + data:byte(offset + 1), offset + 2
end

local function readU32be(data, offset)
    if offset + 3 > #data then return nil end
    local a, b, c, d = data:byte(offset, offset + 3)
    return ((a * 256 + b) * 256 + c) * 256 + d, offset + 4
end

local function little(value, count)
    local bytes = {}
    for index = 1, count do
        local byte = value % 256
        bytes[index] = string.char(byte)
        value = (value - byte) / 256
    end
    return table.concat(bytes)
end

local function readLittle(data, offset, count)
    if offset + count - 1 > #data then return nil end
    local value, factor = 0, 1
    for index = 0, count - 1 do
        value = value + data:byte(offset + index) * factor
        factor = factor * 256
    end
    return value, offset + count
end

local function sessionRetired(origin, session)
    local history = R.retiredSessions and R.retiredSessions[origin]
    return history ~= nil and history.values[tostring(session)] == true
end

local function retireSession(origin, session)
    R.retiredSessions = R.retiredSessions or {}
    local history = R.retiredSessions[origin]
    if not history then
        history = { order = {}, values = {} }
        R.retiredSessions[origin] = history
    end
    local key = tostring(session)
    if history.values[key] then return end
    history.values[key] = true
    history.order[#history.order + 1] = key
    if #history.order > MAX_RETIRED_SESSIONS then
        history.values[table.remove(history.order, 1)] = nil
    end
end

-- ============================================================================
-- Bounded Read-Only VDF & Installed AppManifest Discovery
-- ============================================================================

local function parseVdf(text)
    if type(text) ~= "string" or #text > 2 * 1024 * 1024 then return nil end
    local offset, tokens = 1, 0
    local function token()
        while offset <= #text do
            local c = text:sub(offset, offset)
            if c:match("%s") then
                offset = offset + 1
            elseif text:sub(offset, offset + 1) == "//" then
                offset = (text:find("\n", offset, true) or #text) + 1
            else
                break
            end
        end
        if offset > #text then return nil end
        tokens = tokens + 1
        if tokens > 300000 then error("vdf-token-limit") end
        local c = text:sub(offset, offset)
        offset = offset + 1
        if c == "{" or c == "}" then return c end
        if c ~= '"' then error("vdf-token") end
        local out = {}
        while offset <= #text do
            c = text:sub(offset, offset)
            offset = offset + 1
            if c == '"' then return table.concat(out), true end
            if c == "\\" then
                c = text:sub(offset, offset)
                offset = offset + 1
                if c ~= "\\" and c ~= '"' and c ~= "n" and c ~= "t" then
                    error("vdf-escape")
                end
                if c == "n" then c = "\n" elseif c == "t" then c = "\t" end
            end
            if c == "\0" or #out > 4096 then error("vdf-string") end
            out[#out + 1] = c
        end
        error("vdf-truncated")
    end
    local function object(depth, root)
        if depth > 8 then error("vdf-depth") end
        local out = {}
        while true do
            local key, quoted = token()
            if not key then
                if root then return out end
                error("vdf-truncated")
            end
            if key == "}" and not quoted then
                if root then error("vdf-close") end
                return out
            end
            if not quoted then error("vdf-key") end
            local value, isString = token()
            if value == "{" and not isString then
                value = object(depth + 1, false)
            elseif not isString then
                error("vdf-value")
            end
            if out[key] == nil then
                out[key] = value
            end
        end
    end
    local ok, value = pcall(object, 0, true)
    return ok and value or nil
end

local function readBounded(path, maximum)
    local file, _, code = io.open(path, "rb")
    if not file then return nil, code == 2 and "missing" or "unreadable" end
    local text = file:read(maximum + 1)
    file:close()
    if not text or #text > maximum then return nil, "oversize" end
    return text
end

-- ============================================================================
-- Protocol v3 Snapshot Encoding, Decoding, and Content Key
-- ============================================================================

local function snapshotContentKey(snapshot)
    local parts = {}
    local appIds = snapshot.appIds or {}
    local titles = snapshot.titles or {}
    parts[#parts + 1] = "A" .. tostring(#appIds)
    for _, id in ipairs(appIds) do
        local title = titles[id] or ""
        parts[#parts + 1] = tostring(id) .. ":" .. tostring(#title) .. ":" .. title
    end
    local tombIds = {}
    local tombs = snapshot.tombstones or {}
    for id in pairs(tombs) do tombIds[#tombIds + 1] = id end
    table.sort(tombIds)
    parts[#parts + 1] = "T" .. tostring(#tombIds)
    for _, id in ipairs(tombIds) do
        parts[#parts + 1] = tostring(id) .. "@" .. tostring(tombs[id])
    end
    local instIds = snapshot.installedIds or {}
    local entries = snapshot.entries or {}
    parts[#parts + 1] = "I" .. tostring(#instIds)
    for _, id in ipairs(instIds) do
        local entry = entries[id]
        local name = (entry and entry.name) or ""
        parts[#parts + 1] = tostring(id) .. ":" .. tostring(#name) .. ":" .. name
    end
    return table.concat(parts, "|")
end

local function encodeSnapshotV3(deviceId, appSession, generation, flags, appIds, titles, tombstones, installedEntries)
    if type(deviceId) ~= "string" or #deviceId ~= 32
        or not validInteger(appSession) or not validInteger(generation)
        or not validNonNegativeInteger(flags) or flags > 0xffffffff then
        return nil
    end
    appIds = appIds or {}
    titles = titles or {}
    tombstones = tombstones or {}
    installedEntries = installedEntries or {}
    if #appIds > MAX_APPS then return nil end

    local activeSet = {}
    local appParts = {}
    local prevApp = 0
    for _, appId in ipairs(appIds) do
        if not validInteger(appId) or appId > 0xffffffff or appId <= prevApp then
            return nil
        end
        local title = titles[appId] or ""
        if not sanitizeTitle(title) then title = "" end
        activeSet[appId] = true
        appParts[#appParts + 1] = little(appId, 4) .. u16be(#title) .. title
        prevApp = appId
    end

    local tombIds = {}
    for appId, removedGen in pairs(tombstones) do
        if not activeSet[appId] and validInteger(appId) and appId <= 0xffffffff
            and validInteger(removedGen) and removedGen <= generation then
            tombIds[#tombIds + 1] = appId
        end
    end
    table.sort(tombIds)
    if #tombIds > MAX_TOMBSTONES then
        -- Retain the newest tombstones by removedGeneration, then re-sort by appId.
        table.sort(tombIds, function(a, b)
            if tombstones[a] ~= tombstones[b] then return tombstones[a] > tombstones[b] end
            return a < b
        end)
        local trimmed = {}
        for i = 1, MAX_TOMBSTONES do trimmed[i] = tombIds[i] end
        table.sort(trimmed)
        tombIds = trimmed
    end
    local tombParts = {}
    for _, appId in ipairs(tombIds) do
        tombParts[#tombParts + 1] = little(appId, 4) .. little(tombstones[appId], 8)
    end

    local instIds = {}
    for appId, entry in pairs(installedEntries) do
        if validInteger(appId) and appId <= 0xffffffff
            and type(entry) == "table" and entry.installed == true
            and sanitizeTitle(entry.name) then
            instIds[#instIds + 1] = appId
        end
    end
    table.sort(instIds)
    if #instIds > MAX_APPS then return nil end
    local instParts = {}
    for _, appId in ipairs(instIds) do
        local name = installedEntries[appId].name
        instParts[#instParts + 1] = little(appId, 4) .. string.char(1) .. u16be(#name) .. name
    end

    local originBytes = fromHex(deviceId)
    if not originBytes or #originBytes ~= 16 then return nil end
    local output = table.concat({
        PROTOCOL_MAGIC,
        originBytes,
        little(appSession, 8),
        little(generation, 8),
        little(flags, 4),
        little(#appIds, 4),
        table.concat(appParts),
        little(#tombIds, 4),
        table.concat(tombParts),
        little(#instIds, 4),
        table.concat(instParts),
    })
    if #output > MAX_SNAPSHOT then return nil end
    return output
end

local function decodeSnapshotV3(data, expectedDeviceId, expectedPeerId)
    if type(data) ~= "string" or #data < 56 or #data > MAX_SNAPSHOT
        or data:sub(1, 8) ~= PROTOCOL_MAGIC then
        return nil
    end
    local origin = toHex(data:sub(9, 24))
    if expectedDeviceId and origin == expectedDeviceId then return nil end
    if expectedPeerId and origin ~= expectedPeerId then return nil end

    local session, offset = readLittle(data, 25, 8)
    local generation; generation, offset = readLittle(data, offset, 8)
    local flags; flags, offset = readLittle(data, offset, 4)
    local appCount; appCount, offset = readLittle(data, offset, 4)
    if not validInteger(session) or not validInteger(generation)
        or not flags or not appCount or appCount > MAX_APPS then
        return nil
    end

    local appIds, titles, activeSet = {}, {}, {}
    local prevApp = 0
    for index = 1, appCount do
        local appId; appId, offset = readLittle(data, offset, 4)
        if not appId or appId < 1 or appId <= prevApp then return nil end
        local titleLen; titleLen, offset = readU16be(data, offset)
        if not titleLen or titleLen > 256 or offset + titleLen - 1 > #data then return nil end
        local title = data:sub(offset, offset + titleLen - 1)
        offset = offset + titleLen
        if not sanitizeTitle(title) then return nil end
        appIds[index] = appId
        activeSet[appId] = true
        if title ~= "" then titles[appId] = title end
        prevApp = appId
    end

    local tombCount; tombCount, offset = readLittle(data, offset, 4)
    if not tombCount or tombCount > MAX_TOMBSTONES then return nil end
    local tombstones = {}
    local prevTomb = 0
    for _ = 1, tombCount do
        local appId; appId, offset = readLittle(data, offset, 4)
        if not appId or appId < 1 or appId <= prevTomb or activeSet[appId] then return nil end
        local removedGen; removedGen, offset = readLittle(data, offset, 8)
        if not validInteger(removedGen) or removedGen > generation then return nil end
        tombstones[appId] = removedGen
        prevTomb = appId
    end

    local instCount; instCount, offset = readLittle(data, offset, 4)
    if not instCount or instCount > MAX_APPS then return nil end
    local installedIds, entries = {}, {}
    local prevInst = 0
    for index = 1, instCount do
        local appId; appId, offset = readLittle(data, offset, 4)
        if not appId or appId < 1 or appId <= prevInst then return nil end
        if offset > #data then return nil end
        local stateFlag = data:byte(offset)
        offset = offset + 1
        local nameLen; nameLen, offset = readU16be(data, offset)
        if stateFlag ~= 1 or not nameLen or nameLen > 256 or offset + nameLen - 1 > #data then
            return nil
        end
        local name = data:sub(offset, offset + nameLen - 1)
        offset = offset + nameLen
        if not sanitizeTitle(name) then return nil end
        installedIds[index] = appId
        entries[appId] = {
            appid = appId,
            name = name,
            installed = true,
            ownership = "unknown",
            streamable = "unknown",
        }
        prevInst = appId
    end

    if offset ~= #data + 1 then return nil end
    return {
        origin = origin,
        session = session,
        generation = generation,
        flags = flags,
        appIds = appIds,
        titles = titles,
        tombstones = tombstones,
        installedIds = installedIds,
        entries = entries,
    }
end

-- ============================================================================
-- In-Lua Fallback Transport & Stock AdditionalApps Adapter (Tier 2 Stock Mode)
-- ============================================================================

local function createInMemoryTransportShim()
    local endpoints = {}
    local channels = {}
    local nextEp = 1
    local adapterGen = 0
    local nextGen = 1
    local connectedPeers = {}
    local outbound = {}
    local outboundBytes = 0
    local metrics = {
        peersConnected = 0,
        peersDisconnected = 0,
        messagesReceived = 0,
        messagesQueuedToSend = 0,
        messagesTakenToSend = 0,
        messagesRejected = 0,
        eventOverflows = 0,
        outboundOverflows = 0,
        staleOutboundDropped = 0,
    }

    local function enqueueEvent(ep, ev)
        if ep.overflowed then
            metrics.eventOverflows = metrics.eventOverflows + 1
            return false
        end
        local bytes = #ev.type + #(ev.peer and ev.peer.id or "") + #(ev.payload or "") + 32
        if #ep.events >= 32 or ep.eventBytes + bytes > 128 * 1024 then
            metrics.eventOverflows = metrics.eventOverflows + 1
            ep.events = {}
            ep.eventBytes = 0
            ep.overflowed = true
            return false
        end
        ep.events[#ep.events + 1] = ev
        ep.eventBytes = ep.eventBytes + bytes
        return true
    end

    local T = {}
    function T.open(channel, _onReady)
        if channels[channel] then return 0 end
        local id = nextEp
        nextEp = nextEp + 1
        local ep = { channel = channel, events = {}, eventBytes = 0, overflowed = false }
        endpoints[id] = ep
        channels[channel] = id
        for _, peer in pairs(connectedPeers) do
            enqueueEvent(ep, { type = "connected", peer = peer, channel = channel, payload = "" })
        end
        return id
    end
    function T.close(id)
        local ep = endpoints[id]
        if not ep then return true end
        channels[ep.channel] = nil
        endpoints[id] = nil
        return true
    end
    function T.installAdapter(_name)
        if adapterGen ~= 0 then return 0 end
        adapterGen = nextGen
        nextGen = nextGen + 1
        return adapterGen
    end
    function T.removeAdapter(gen)
        if gen == 0 or gen ~= adapterGen then return false end
        adapterGen = 0
        for _, peer in pairs(connectedPeers) do
            for _, ep in pairs(endpoints) do
                enqueueEvent(ep, { type = "disconnected", peer = peer, channel = ep.channel, payload = "" })
            end
            metrics.peersDisconnected = metrics.peersDisconnected + 1
        end
        connectedPeers = {}
        outbound = {}
        outboundBytes = 0
        return true
    end
    function T.announcePeer(gen, peerId, session, authenticated)
        if gen ~= adapterGen or not authenticated then
            metrics.messagesRejected = metrics.messagesRejected + 1
            return false
        end
        local existing = connectedPeers[peerId]
        if existing then
            if existing.session == session then return true end
            for _, ep in pairs(endpoints) do
                enqueueEvent(ep, { type = "disconnected", peer = existing, channel = ep.channel, payload = "" })
            end
            metrics.peersDisconnected = metrics.peersDisconnected + 1
        end
        local peer = { id = peerId, session = session }
        connectedPeers[peerId] = peer
        for _, ep in pairs(endpoints) do
            enqueueEvent(ep, { type = "connected", peer = peer, channel = ep.channel, payload = "" })
        end
        metrics.peersConnected = metrics.peersConnected + 1
        return true
    end
    function T.disconnectPeer(gen, peerId, session)
        if gen ~= adapterGen then return false end
        local existing = connectedPeers[peerId]
        if not existing or existing.session ~= session then return false end
        connectedPeers[peerId] = nil
        for _, ep in pairs(endpoints) do
            enqueueEvent(ep, { type = "disconnected", peer = existing, channel = ep.channel, payload = "" })
        end
        metrics.peersDisconnected = metrics.peersDisconnected + 1
        return true
    end
    function T.deliver(gen, peerId, session, channel, payload)
        if gen ~= adapterGen or #payload > 65536 then
            metrics.messagesRejected = metrics.messagesRejected + 1
            return false
        end
        local peer = connectedPeers[peerId]
        local epId = channels[channel]
        if not peer or peer.session ~= session or not epId then
            metrics.messagesRejected = metrics.messagesRejected + 1
            return false
        end
        if not enqueueEvent(endpoints[epId], {
            type = "message", peer = peer, channel = channel, payload = payload,
        }) then
            return false
        end
        metrics.messagesReceived = metrics.messagesReceived + 1
        return true
    end
    function T.send(epId, peerId, payload)
        local ep = endpoints[epId]
        local peer = connectedPeers[peerId]
        if adapterGen == 0 or not ep or not peer or #payload > 65536 then
            metrics.messagesRejected = metrics.messagesRejected + 1
            return false
        end
        local bytes = #payload + #peerId + #ep.channel + 32
        if #outbound >= 128 or outboundBytes + bytes > 1024 * 1024 then
            metrics.outboundOverflows = metrics.outboundOverflows + 1
            return false
        end
        outbound[#outbound + 1] = {
            endpoint = epId,
            peer = peer,
            channel = ep.channel,
            payload = payload,
        }
        outboundBytes = outboundBytes + bytes
        metrics.messagesQueuedToSend = metrics.messagesQueuedToSend + 1
        return true
    end
    function T.takeOutbound(gen, maximum)
        local out = {}
        if gen ~= adapterGen or maximum < 1 then return out end
        while #outbound > 0 and #out < maximum do
            local msg = table.remove(outbound, 1)
            outboundBytes = math.max(0, outboundBytes - (#msg.payload + #msg.peer.id + #msg.channel + 32))
            local active = connectedPeers[msg.peer.id]
            if not active or active.session ~= msg.peer.session then
                metrics.staleOutboundDropped = metrics.staleOutboundDropped + 1
            else
                out[#out + 1] = msg
                metrics.messagesTakenToSend = metrics.messagesTakenToSend + 1
            end
        end
        return out
    end
    function T.poll(epId, maximum)
        local out = {}
        local ep = endpoints[epId]
        if not ep or maximum < 1 then return out end
        if ep.overflowed then
            out[#out + 1] = { type = "overflow", channel = ep.channel, payload = "" }
            ep.overflowed = false
        end
        while #out < maximum and #ep.events > 0 do
            local ev = table.remove(ep.events, 1)
            local bytes = #ev.type + #(ev.peer and ev.peer.id or "") + #(ev.payload or "") + 32
            ep.eventBytes = math.max(0, ep.eventBytes - bytes)
            out[#out + 1] = ev
        end
        return out
    end
    function T.peers()
        local out = {}
        for _, p in pairs(connectedPeers) do out[#out + 1] = p end
        return out
    end
    function T.metrics() return metrics end
    return T
end

local function detectManagedApis()
    if type(SLS) ~= "table"
        or type(SLS.onTick) ~= "function"
        or type(SLS.onShutdown) ~= "function"
        or type(SLS.cancelCallback) ~= "function"
        or type(SLS.Transport) ~= "table"
        or type(SLS.RuntimeApps) ~= "table" then
        return false
    end
    for _, name in ipairs({
        "open", "close", "send", "poll", "peers",
        "installAdapter", "removeAdapter", "announcePeer",
        "disconnectPeer", "deliver", "takeOutbound",
    }) do
        if type(SLS.Transport[name]) ~= "function" then return false end
    end
    for _, name in ipairs({ "open", "close", "replace" }) do
        if type(SLS.RuntimeApps[name]) ~= "function" then return false end
    end
    return true
end

-- ============================================================================
-- Direct Authenticated Nonblocking Peer Backend (Tier 1 & Tier 2 Unified Core)
-- ============================================================================

local function createPeerBackend(options)
    if not ensureLinuxFfi() then return nil, "ffi-unavailable" end
    local settings, settingsErr = resolveSettings()
    if not settings then return nil, settingsErr end

    local managed = detectManagedApis()
    local tier = managed and "managed-owner" or "stock-opportunistic"
    local transportApi = managed and SLS.Transport or createInMemoryTransportShim()

    local provider = 0
    if managed then
        provider = SLS.RuntimeApps.open("sls.remote-play-sync.v1")
        if provider == 0 then return nil, "generic-resource-unavailable" end
    end
    local endpoint = transportApi.open(CHANNEL, function() end)
    local adapter = transportApi.installAdapter(ADAPTER_NAME)
    if endpoint == 0 or adapter == 0 then
        if provider ~= 0 then SLS.RuntimeApps.close(provider) end
        if endpoint ~= 0 then transportApi.close(endpoint) end
        if adapter ~= 0 then transportApi.removeAdapter(adapter) end
        return nil, "generic-resource-unavailable"
    end

    local appSessionBytes = randomBytes(6)
    if not appSessionBytes then
        transportApi.close(endpoint)
        transportApi.removeAdapter(adapter)
        if provider ~= 0 then SLS.RuntimeApps.close(provider) end
        return nil, "random-unavailable"
    end
    local appSession = 0
    for index = 1, 6 do
        appSession = appSession + appSessionBytes:byte(index) * 256 ^ (index - 1)
    end
    if appSession == 0 then appSession = 1 end

    local mode = settings.mode
    local deviceId = settings.deviceId
    local peerId = settings.peerId
    local psk = settings.psk
    local hasListener = (mode == "listen" or mode == "auto")
    local hasConnector = (mode == "connect" or mode == "auto")
    local prefersClientRole = deviceId < peerId

    local HANDSHAKE_TIMEOUT_MS = managed and 10000 or 120000
    local CANDIDATE_TIMEOUT_MS = managed and 5000 or 120000
    local IDLE_TIMEOUT_MS = managed and 20000 or 300000
    local HEARTBEAT_INTERVAL_MS = managed and 5000 or 15000
    local RECONCILE_INTERVAL_MS = 5000

    local backend = {
        tier = tier,
        settings = settings,
        appSession = appSession,
    }
    local connection = nil
    local inboundCandidate = nil
    local listener = -1
    local socketsReady = false
    local stopped = false
    local stoppingFromShutdown = false
    local tickHandle = 0
    local shutdownHandle = 0
    local retryDelay = 100
    local retryAt = (mode == "auto" and not prefersClientRole) and (nowMs() + 250) or 0
    local acceptRetryAt = 0
    local acceptBackoffMs = 50
    local assemblies = {}
    local pendingSnapshot = nil
    local failedApply = nil
    local nextReconcile = 0
    local lastHeartbeat = 0
    local lastOpportunisticStepAt = 0
    local receiveBuffer = ffi.new("uint8_t[65536]")

    R.threadId = threadId
    evidence("loaded tid=" .. threadId() .. " tier=" .. tier .. " device=" .. deviceId)

    local function sockaddr(address, addressPort)
        local result = ffi.new("struct sls_rps_sockaddr_in[1]")
        result[0].sin_family = AF_INET
        result[0].sin_port = bit.bor(
            bit.lshift(bit.band(addressPort, 0xff), 8),
            bit.rshift(addressPort, 8)
        )
        if ffi.C.inet_pton(AF_INET, address, result[0].sin_addr) ~= 1 then return nil end
        return result
    end

    local function newSocket()
        local fd = ffi.C.socket(AF_INET, bit.bor(SOCK_STREAM, SOCK_NONBLOCK, SOCK_CLOEXEC), 0)
        if fd >= 0 then
            local sndBuf = ffi.new("int[1]", 262144)
            ffi.C.setsockopt(fd, SOL_SOCKET, SO_SNDBUF, sndBuf, 4)
        end
        return fd
    end

    local function frame(body)
        return u32be(#body) .. body
    end

    local function queueBody(conn, body)
        local encoded = frame(body)
        if #body > MAX_FRAME or conn.writeBytes + #encoded > MAX_WRITE_BYTES then return false end
        conn.writes[#conn.writes + 1] = encoded
        conn.writeBytes = conn.writeBytes + #encoded
        return true
    end

    local function transcript(conn)
        return "SLSRPS-AUTH-v1" .. conn.clientId .. conn.serverId
            .. conn.clientNonce .. conn.serverNonce
    end

    local function derive(conn)
        local base = hmacSha256(psk, transcript(conn) .. "session")
        if not base then return false end
        local c2s = hmacSha256(base, "client-to-server")
        local s2c = hmacSha256(base, "server-to-client")
        local sessionKey = hmacSha256(base, "session-id")
        if not c2s or not s2c or not sessionKey then return false end
        if conn.role == "client" then
            conn.sendKey, conn.recvKey = c2s, s2c
        else
            conn.sendKey, conn.recvKey = s2c, c2s
        end
        conn.sessionId = toHex(sessionKey:sub(1, 16))
        conn.sendSequence, conn.recvSequence = 0, 0
        return true
    end

    local function dropCandidate(reason)
        local cand = inboundCandidate
        inboundCandidate = nil
        if cand then closeFd(cand.fd) end
        if reason then
            R.authFailures = (R.authFailures or 0) + 1
            acceptRetryAt = nowMs() + acceptBackoffMs
            acceptBackoffMs = math.min(acceptBackoffMs * 2, 2000)
        end
    end

    local function markRemoteDisconnected()
        local remote = R.remoteLibraries and R.remoteLibraries[peerId]
        if remote then
            remote.deviceAvailable = false
            remote.disconnectedAt = nowMs()
        end
    end

    local function drop(reason)
        local conn = connection
        connection = nil
        assemblies = {}
        failedApply = nil
        markRemoteDisconnected()
        if pendingSnapshot then
            pendingSnapshot.index = 1
            pendingSnapshot.retryAt = 0
        end
        local wasEstablished = false
        if conn then
            wasEstablished = conn.announced == true
            if conn.announced then
                transportApi.disconnectPeer(adapter, peerId, conn.sessionId)
            end
            closeFd(conn.fd)
        end
        if hasConnector and not stopped then
            local jitter = (mode == "auto" and not prefersClientRole) and 150 or 0
            retryAt = nowMs() + retryDelay + jitter
            retryDelay = math.min(retryDelay * 2, 5000)
        end
        if reason and reason ~= "eof" and reason ~= "replaced-by-authenticated-peer" then
            if wasEstablished or (reason ~= "connect" and reason ~= "handshake-timeout") then
                logWarn("RemotePlaySync connection closed: " .. reason)
            else
                R.connectRetries = (R.connectRetries or 0) + 1
                if R.connectRetries == 1 then
                    logDebug("RemotePlaySync peer unreachable (" .. reason .. "); retrying in background")
                end
            end
        end
    end

    local function establish(conn)
        if not derive(conn) then return false end
        local t = nowMs()
        if conn == inboundCandidate then
            -- Simultaneous-open tie-breaker in MODE=auto:
            -- If we prefer our outbound "client" socket and it is either actively
            -- handshaking or freshly established (< 2s ago with recent traffic),
            -- discard the redundant inbound socket so both sides converge on one TCP stream.
            if mode == "auto" and prefersClientRole and connection and connection.role == "client" then
                local freshConnect = connection.state ~= "established"
                    and (t - connection.startedAt < 2000)
                local freshEstablished = connection.state == "established"
                    and (t - (connection.establishedAt or t) < 2000)
                    and (t - (connection.lastRxAt or t) < 1500)
                if freshConnect or freshEstablished then
                    inboundCandidate = nil
                    closeFd(conn.fd)
                    return true
                end
            end
            inboundCandidate = nil
            if connection then
                R.halfOpenReplacements = (R.halfOpenReplacements or 0) + 1
                drop("replaced-by-authenticated-peer")
            end
            connection = conn
        end
        if not transportApi.announcePeer(adapter, peerId, conn.sessionId, true) then
            return false
        end
        conn.announced = true
        conn.state = "established"
        conn.establishedAt = t
        conn.lastRxAt = t
        acceptBackoffMs = 50
        retryDelay = 100
        R.connectRetries = 0
        if pendingSnapshot then
            pendingSnapshot.index = 1
            pendingSnapshot.retryAt = 0
        end
        logInfo(string.format("RemotePlaySync session established with peer %s (role=%s)", peerId, conn.role))
        evidence("authenticated tid=" .. threadId() .. " role=" .. conn.role .. " session=" .. conn.sessionId)
        return true
    end

    local function makeConnection(fd, role, state)
        return {
            fd = fd,
            role = role,
            state = state,
            read = "",
            writes = {},
            writeOffset = 1,
            writeBytes = 0,
            announced = false,
            startedAt = nowMs(),
        }
    end

    local function sendHello(conn)
        conn.clientId, conn.serverId = deviceId, peerId
        conn.clientNonce = randomBytes(32)
        if not conn.clientNonce then return false end
        conn.state = "wait-server"
        return queueBody(conn, string.char(1) .. deviceId .. conn.clientNonce)
    end

    local function handleHandshake(conn, body)
        local kind = body:byte(1)
        if conn.state == "wait-hello" and kind == 1 and #body == 65 then
            conn.clientId, conn.serverId = body:sub(2, 33):lower(), deviceId
            if conn.clientId ~= peerId then
                R.authFailures = (R.authFailures or 0) + 1
                return false
            end
            conn.clientNonce = body:sub(34, 65)
            conn.serverNonce = randomBytes(32)
            if not conn.serverNonce then return false end
            local tag = hmacSha256(psk, transcript(conn) .. "server")
            conn.state = "wait-client"
            return tag and queueBody(conn, string.char(2) .. deviceId .. conn.serverNonce .. tag)
        elseif conn.state == "wait-server" and kind == 2 and #body == 97 then
            conn.serverId = body:sub(2, 33):lower()
            conn.serverNonce = body:sub(34, 65)
            if conn.serverId ~= peerId then
                R.authFailures = (R.authFailures or 0) + 1
                return false
            end
            local expected = hmacSha256(psk, transcript(conn) .. "server")
            if not expected or not secureEqual(expected, body:sub(66, 97)) then
                R.authFailures = (R.authFailures or 0) + 1
                return false
            end
            local tag = hmacSha256(psk, transcript(conn) .. "client")
            return tag and queueBody(conn, string.char(3) .. tag) and establish(conn)
        elseif conn.state == "wait-client" and kind == 3 and #body == 33 then
            local expected = hmacSha256(psk, transcript(conn) .. "client")
            if not expected or not secureEqual(expected, body:sub(2, 33)) then
                R.authFailures = (R.authFailures or 0) + 1
                return false
            end
            return establish(conn)
        end
        R.authFailures = (R.authFailures or 0) + 1
        return false
    end

    local function queueData(conn, channel, payload)
        if #channel < 1 or #channel > 64 or #payload > 65536 then return false end
        local nextSequence = conn.sendSequence + 1
        if nextSequence > 0xffffffff then return false end
        local content = string.char(4) .. u32be(nextSequence)
            .. string.char(#channel) .. channel .. payload
        local tag = hmacSha256(conn.sendKey, content)
        if not tag or not queueBody(conn, content .. tag) then return false end
        conn.sendSequence = nextSequence
        return true
    end

    local function handleData(conn, body)
        if conn.state ~= "established" or body:byte(1) ~= 4 or #body < 38 then
            R.framesRejected = (R.framesRejected or 0) + 1
            return false
        end
        local sequence, offset = readU32be(body, 2)
        local channelLength = body:byte(offset)
        offset = offset + 1
        if not sequence or sequence ~= conn.recvSequence + 1
            or channelLength < 1 or channelLength > 64
            or offset + channelLength + 32 - 1 > #body then
            R.framesRejected = (R.framesRejected or 0) + 1
            return false
        end
        local tagOffset = #body - 31
        local content, tag = body:sub(1, tagOffset - 1), body:sub(tagOffset)
        local expectedTag = hmacSha256(conn.recvKey, content)
        if not expectedTag or not secureEqual(expectedTag, tag) then
            R.framesRejected = (R.framesRejected or 0) + 1
            return false
        end
        local channel = body:sub(offset, offset + channelLength - 1)
        local payload = body:sub(offset + channelLength, tagOffset - 1)
        if #payload > 65536 then
            R.framesRejected = (R.framesRejected or 0) + 1
            return false
        end
        conn.recvSequence = sequence
        conn.lastRxAt = nowMs()
        if channel == HEARTBEAT_CHANNEL then return payload == "ping" end
        return transportApi.deliver(adapter, peerId, conn.sessionId, channel, payload)
    end

    local function processFrames(conn)
        local processed = 0
        while processed < 8 and #conn.read >= 4 do
            local length = readU32be(conn.read, 1)
            if not length or length < 1 or length > MAX_FRAME then
                R.framesRejected = (R.framesRejected or 0) + 1
                return false
            end
            if #conn.read < 4 + length then break end
            local body = conn.read:sub(5, 4 + length)
            conn.read = conn.read:sub(5 + length)
            local wasEstablished = (conn.state == "established")
            local valid
            if wasEstablished then
                valid = handleData(conn, body)
            else
                valid = handleHandshake(conn, body)
            end
            if not valid then return false end
            processed = processed + 1
            -- If an inboundCandidate just promoted itself into `connection`
            -- (or closed itself in tie-break), or if handshake just completed
            -- (so `"connected"` event & initial outbound snapshot flush run before
            -- post-handshake data delivery), yield remaining buffered bytes to next pass.
            if conn ~= connection and conn ~= inboundCandidate then break end
            if not wasEstablished and conn.state == "established" then break end
        end
        return true
    end

    local function readConnection(conn)
        if not processFrames(conn) then return false end
        if conn ~= connection and conn ~= inboundCandidate then return true end
        local count = tonumber(ffi.C.recv(conn.fd, receiveBuffer, 65536, 0))
        if count and count > 0 then
            conn.read = conn.read .. ffi.string(receiveBuffer, count)
            if #conn.read > MAX_READ_BUFFER or not processFrames(conn) then return false end
        elseif count == 0 then
            return false
        elseif not count or (ffi.errno() ~= EAGAIN and ffi.errno() ~= EINTR) then
            return false
        end
        return true
    end

    local function flush(conn)
        local budget = 262144
        while budget > 0 and #conn.writes > 0 do
            local first = conn.writes[1]
            local remaining = #first - conn.writeOffset + 1
            local requested = math.min(remaining, budget)
            local pointer = ffi.cast("const uint8_t*", first) + conn.writeOffset - 1
            local count = tonumber(ffi.C.send(conn.fd, pointer, requested, MSG_NOSIGNAL))
            if count and count > 0 then
                if count < requested then R.partialWrites = (R.partialWrites or 0) + 1 end
                conn.writeOffset = conn.writeOffset + count
                conn.writeBytes = conn.writeBytes - count
                budget = budget - count
                if conn.writeOffset > #first then
                    table.remove(conn.writes, 1)
                    conn.writeOffset = 1
                end
            elseif count and count < 0 and (ffi.errno() == EAGAIN or ffi.errno() == EINTR) then
                return true
            else
                return false
            end
        end
        return true
    end

    local function openListener()
        if not hasListener or listener >= 0 then return true end
        local fd = newSocket()
        if fd < 0 then return false end
        local one = ffi.new("int[1]", 1)
        ffi.C.setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, one, ffi.sizeof(one))
        local address = sockaddr(settings.bindHost, settings.bindPort)
        if not address
            or ffi.C.bind(fd, ffi.cast("struct sls_rps_sockaddr*", address), ffi.sizeof(address[0])) ~= 0
            or ffi.C.listen(fd, 8) ~= 0 then
            closeFd(fd)
            return false
        end
        listener = fd
        return true
    end

    local function acceptConnection(currentTime)
        if listener < 0 or inboundCandidate or currentTime < acceptRetryAt then return end
        -- If there is no primary connection at all, accept directly into `connection`;
        -- if a primary connection exists (potentially half-open after Steam Deck suspend),
        -- accept into `inboundCandidate` and only replace `connection` AFTER full mutual HMAC!
        if connection and connection.state ~= "established" and connection.role == "server" then
            return
        end
        local deadFlags = bit.bor(POLLRDHUP, POLLHUP, POLLERR, POLLNVAL)
        local pfd = ffi.new("struct sls_rps_pollfd[1]")
        for _ = 1, 8 do
            local fd = ffi.C.accept4(listener, nil, nil, bit.bor(SOCK_NONBLOCK, SOCK_CLOEXEC))
            if fd < 0 then break end
            pfd[0].fd = fd
            pfd[0].events = bit.bor(POLLIN, POLLRDHUP)
            pfd[0].revents = 0
            -- Any socket still in the listen backlog cannot have received ServerHello yet,
            -- so if the client already sent FIN/RST (CLOSE-WAIT), drain and discard immediately.
            if ffi.C.poll(pfd, 1, 0) > 0 and bit.band(pfd[0].revents, deadFlags) ~= 0 then
                closeFd(fd)
                R.staleBacklogDrained = (R.staleBacklogDrained or 0) + 1
            else
                if not connection then
                    connection = makeConnection(fd, "server", "wait-hello")
                else
                    inboundCandidate = makeConnection(fd, "server", "wait-hello")
                end
                break
            end
        end
    end

    local function startConnect(currentTime)
        if not hasConnector or connection or inboundCandidate or currentTime < retryAt then
            return
        end
        local fd = newSocket()
        local address = fd >= 0 and sockaddr(settings.peerHost, settings.peerPort) or nil
        if fd < 0 or not address then
            closeFd(fd)
            retryAt = currentTime + retryDelay
            return
        end
        local result = ffi.C.connect(fd, ffi.cast("struct sls_rps_sockaddr*", address), ffi.sizeof(address[0]))
        if result == 0 then
            connection = makeConnection(fd, "client", "connecting")
            if not sendHello(connection) then drop("hello") end
        elseif ffi.errno() == EINPROGRESS then
            connection = makeConnection(fd, "client", "connecting")
        else
            closeFd(fd)
            retryAt = currentTime + retryDelay
            retryDelay = math.min(retryDelay * 2, 5000)
        end
    end

    local function finishConnect(conn)
        if conn.state ~= "connecting" then return true end
        local descriptor = ffi.new("struct sls_rps_pollfd[1]")
        descriptor[0].fd = conn.fd
        descriptor[0].events = POLLOUT
        if ffi.C.poll(descriptor, 1, 0) <= 0 then return true end
        local errorValue = ffi.new("int[1]")
        local errorLength = ffi.new("uint32_t[1]", 4)
        if ffi.C.getsockopt(conn.fd, SOL_SOCKET, SO_ERROR, errorValue, errorLength) ~= 0
            or errorValue[0] ~= 0 then
            return false
        end
        return sendHello(conn)
    end

    local function chunkSnapshot(snapshotBytes, generation)
        local total = math.ceil(#snapshotBytes / CHUNK_DATA)
        local result = {}
        for index = 1, total do
            local header = "SLSC" .. little(appSession, 8) .. little(generation, 8)
                .. u16be(index) .. u16be(total) .. u32be(#snapshotBytes)
            result[index] = header .. snapshotBytes:sub(
                (index - 1) * CHUNK_DATA + 1,
                math.min(index * CHUNK_DATA, #snapshotBytes)
            )
        end
        return result
    end

    local function acceptChunk(event)
        local data = event.payload
        if type(data) ~= "string" or #data < 28 or data:sub(1, 4) ~= "SLSC" then
            R.framesRejected = (R.framesRejected or 0) + 1
            return nil
        end
        local session, offset = readLittle(data, 5, 8)
        local generation; generation, offset = readLittle(data, offset, 8)
        local index; index, offset = readU16be(data, offset)
        local total; total, offset = readU16be(data, offset)
        local length; length, offset = readU32be(data, offset)
        if not validInteger(session) or not validInteger(generation)
            or not index or not total or index < 1 or index > total or total > MAX_CHUNKS
            or not length or length < 56 or length > MAX_SNAPSHOT
            or total ~= math.ceil(length / CHUNK_DATA)
            or (#data - offset + 1) ~= math.min(CHUNK_DATA, length - (index - 1) * CHUNK_DATA) then
            R.framesRejected = (R.framesRejected or 0) + 1
            return nil
        end
        local key = event.peer.id .. ":" .. tostring(session) .. ":" .. tostring(generation)
        local assembly = assemblies[key]
        if not assembly then
            assemblies = {}
            assembly = { total = total, length = length, parts = {}, bytes = 0 }
            assemblies[key] = assembly
        end
        if assembly.total ~= total or assembly.length ~= length then
            assemblies[key] = nil
            R.framesRejected = (R.framesRejected or 0) + 1
            return nil
        end
        local partBytes = data:sub(offset)
        if assembly.parts[index] and assembly.parts[index] ~= partBytes then
            assemblies[key] = nil
            R.framesRejected = (R.framesRejected or 0) + 1
            return nil
        end
        if not assembly.parts[index] then
            assembly.parts[index] = partBytes
            assembly.bytes = assembly.bytes + #partBytes
        end
        if assembly.bytes > length then
            assemblies[key] = nil
            R.framesRejected = (R.framesRejected or 0) + 1
            return nil
        end
        for part = 1, total do
            if not assembly.parts[part] then return nil end
        end
        local complete = table.concat(assembly.parts)
        assemblies[key] = nil
        if #complete ~= length then
            R.framesRejected = (R.framesRejected or 0) + 1
            return nil
        end
        local decoded = decodeSnapshotV3(complete, deviceId, peerId)
        if not decoded then
            R.framesRejected = (R.framesRejected or 0) + 1
        end
        return decoded
    end

    local function applyStockAdditionalApps()
        if not SLS or not SLS.config or type(SLS.config.setAdditionalApps) ~= "function" then
            return false
        end
        local engine = SLS.steamEngine
        -- Note: CSteamEngine::getUser(const uint32_t index = 0) loses its C++ default argument
        -- when bound via LuaBridge3 (.addFunction("getUser", &CSteamEngine::getUser)), so index 0
        -- MUST be passed explicitly.
        local okUser, user = false, nil
        if engine and type(engine.getUser) == "function" then
            okUser, user = pcall(function() return engine:getUser(0) end)
        end
        local okClient, clientUser = false, nil
        if okUser and user and type(user.getClientUser) == "function" then
            okClient, clientUser = pcall(function() return user:getClientUser() end)
        end
        local okLoggedOn, loggedOn = false, false
        if okClient and clientUser and type(clientUser.loggedOn) == "function" then
            okLoggedOn, loggedOn = pcall(function() return clientUser:loggedOn() end)
        end
        -- Defer modifying AdditionalApps until Steam has logged on so CUser:isSubscribed()
        -- reflects Valve's populated license map and never touches genuinely owned games.
        if not okUser or not user or not okClient or not clientUser
            or not okLoggedOn or not loggedOn then
            R._stockPendingApply = true
            return true
        end
        local effective = {}
        local localCount = 0
        for appId in pairs(R._stockLocalConfigApps or {}) do
            effective[appId] = true
            localCount = localCount + 1
        end
        local protectedCount = 0
        local peerCount = 0
        for _, remoteSet in pairs(R.remoteAdditionalApps or {}) do
            peerCount = peerCount + 1
            for appId in pairs(remoteSet) do
                if not effective[appId] then
                    local okSub, subscribed = pcall(function() return user:isSubscribed(appId) end)
                    if okSub and subscribed == true then
                        protectedCount = protectedCount + 1
                    else
                        effective[appId] = true
                    end
                end
            end
        end
        if peerCount > 0 then
            R._stockHadRemoteSync = true
        end
        R.ownershipProtectedCount = protectedCount
        local effectiveList = sortedList(effective)
        local key = table.concat(effectiveList, ",")
        if key ~= R._stockAppliedEffectiveKey then
            local okSet, setErr = pcall(function()
                SLS.config:setAdditionalApps(effectiveList, false)
            end)
            if not okSet then
                logWarn("RemotePlaySync setAdditionalApps failed: " .. tostring(setErr))
                return false
            end
            R._stockAppliedEffectiveKey = key
            if R._stockHadRemoteSync then
                logInfo(string.format(
                    "RemotePlaySync applied library state (local=%d, remote_peers=%d, effective=%d, protected_owned=%d)",
                    localCount, peerCount, #effectiveList, protectedCount
                ))
            end
        end
        R._stockPendingApply = false
        return true
    end

    function backend.capabilities()
        if managed then
            return {
                available = true,
                transport = "lua-direct-tcp-hmac-v3",
                tier = tier,
                reason = "",
            }
        end
        return {
            available = true,
            transport = "lua-direct-tcp-hmac-v3-opportunistic",
            tier = tier,
            reason = socketsReady and "stock-opportunistic-cm-driven"
                or "stock-deferred-until-initialized",
        }
    end

    function backend.activateSockets()
        if stopped or socketsReady then return socketsReady end
        if hasListener and not openListener() then
            return false, "listen-failed"
        end
        socketsReady = true
        return true
    end

    function backend.invalidate()
        pendingSnapshot = nil
    end

    function backend.publish(generation, appIds, titles, tombstones, installedEntries, _force)
        local flags = 1
        if settings.syncInstalled and installedEntries then flags = bit.bor(flags, 2) end
        if not managed then flags = bit.bor(flags, 4) end
        local snapshotBytes = encodeSnapshotV3(
            deviceId, appSession, generation, flags,
            appIds, titles, tombstones, settings.syncInstalled and installedEntries or {}
        )
        if not snapshotBytes then
            pendingSnapshot = nil
            return false
        end
        pendingSnapshot = {
            chunks = chunkSnapshot(snapshotBytes, generation),
            index = 1,
            generation = generation,
            retryAt = 0,
        }
        return true
    end

    function backend.apply(snapshot)
        if REMOTE_PLAY_SYNC_TEST_MODE and type(REMOTE_PLAY_SYNC_TEST_APPLY) == "function" then
            if not REMOTE_PLAY_SYNC_TEST_APPLY(snapshot) then return false end
        end
        local remoteAppSet = normalizedSet(snapshot.appIds)
        R.remoteAdditionalApps[snapshot.origin] = remoteAppSet
        R.remoteTombstones[snapshot.origin] = snapshot.tombstones or {}
        R.remoteTitles[snapshot.origin] = snapshot.titles or {}
        R.remoteLibraries[snapshot.origin] = {
            session = snapshot.session,
            generation = snapshot.generation,
            additionalAppIds = snapshot.appIds,
            titles = snapshot.titles or {},
            tombstones = snapshot.tombstones or {},
            appIds = snapshot.installedIds or {},
            entries = snapshot.entries or {},
            observedAt = nowMs(),
            deviceAvailable = true,
            ownership = "preserved",
            streamable = "unknown",
        }
        if managed then
            return SLS.RuntimeApps.replace(provider, snapshot.origin, snapshot.appIds)
        end
        return applyStockAdditionalApps()
    end

    function backend.refreshStockEffective()
        if not managed then
            R._stockAppliedEffectiveKey = nil
            return applyStockAdditionalApps()
        end
        return true
    end

    function backend.stop()
        if stopped then return end
        stopped = true
        if managed and not stoppingFromShutdown then
            if tickHandle ~= 0 then SLS.cancelCallback(tickHandle) end
            if shutdownHandle ~= 0 then SLS.cancelCallback(shutdownHandle) end
        end
        dropCandidate(nil)
        if connection then drop(nil) end
        closeFd(listener)
        listener = -1
        socketsReady = false
        transportApi.close(endpoint)
        transportApi.removeAdapter(adapter)
        if managed and provider ~= 0 then
            SLS.RuntimeApps.close(provider)
            provider = 0
        end
    end

    local function acknowledge(snapshot)
        return transportApi.send(
            endpoint, peerId,
            "SLSA" .. little(snapshot.session, 8) .. little(snapshot.generation, 8)
        )
    end

    local function applyOrRetry(snapshot)
        local previous = R.peers[snapshot.origin]
        if previous and previous.session == snapshot.session
            and previous.generation > snapshot.generation then
            R.duplicatesIgnored = (R.duplicatesIgnored or 0) + 1
            return
        end
        local contentKey = snapshotContentKey(snapshot)
        local duplicate = previous and previous.session == snapshot.session
            and previous.generation == snapshot.generation
        if duplicate and previous.contentKey ~= contentKey then
            R.framesRejected = (R.framesRejected or 0) + 1
            drop("generation-conflict")
            return
        end
        if duplicate then
            local current = R.remoteLibraries[snapshot.origin]
            if current then
                current.observedAt = nowMs()
                current.deviceAvailable = true
            end
            R.duplicatesIgnored = (R.duplicatesIgnored or 0) + 1
            failedApply = nil
            acknowledge(snapshot)
            return
        end
        if options.onSnapshot(snapshot, contentKey) then
            failedApply = nil
            acknowledge(snapshot)
        else
            failedApply = { snapshot = snapshot, retryAt = nowMs() + 500 }
        end
    end

    local function processEndpointEvents()
        local events = transportApi.poll(endpoint, 32)
        for _, event in ipairs(events) do
            if event.type == "connected" then
                options.onPeerConnected(event.peer)
            elseif event.type == "disconnected" then
                markRemoteDisconnected()
            elseif event.type == "message" then
                if event.payload:sub(1, 4) == "SLSA" and #event.payload == 20 then
                    local session, offset = readLittle(event.payload, 5, 8)
                    local generation = readLittle(event.payload, offset, 8)
                    if session == appSession and pendingSnapshot
                        and pendingSnapshot.generation == generation then
                        pendingSnapshot = nil
                        R.snapshotsAcked = (R.snapshotsAcked or 0) + 1
                    end
                else
                    local snapshot = acceptChunk(event)
                    if snapshot then applyOrRetry(snapshot) end
                end
            elseif event.type == "overflow" then
                assemblies = {}
                if pendingSnapshot then
                    pendingSnapshot.index = 1
                    pendingSnapshot.retryAt = 0
                end
            end
        end
    end

    local function tick()
        if stopped or not socketsReady then return end
        local currentTime = nowMs()

        if settings.syncInstalled then
            options.advanceSource(currentTime)
        end
        if not managed and R._stockPendingApply then
            applyStockAdditionalApps()
        end

        local remote = R.remoteLibraries[peerId]
        if remote and remote.deviceAvailable and currentTime - remote.observedAt > IDLE_TIMEOUT_MS then
            remote.deviceAvailable = false
        end

        if currentTime >= nextReconcile then
            options.reconcile()
            nextReconcile = currentTime + RECONCILE_INTERVAL_MS
        end

        if hasListener then acceptConnection(currentTime) end
        if hasConnector then startConnect(currentTime) end

        -- Drive unauthenticated inboundCandidate handshake alongside active connection
        if inboundCandidate then
            if currentTime - inboundCandidate.startedAt > CANDIDATE_TIMEOUT_MS then
                dropCandidate("candidate-timeout")
            elseif not readConnection(inboundCandidate) then
                dropCandidate("candidate-io")
            elseif inboundCandidate and not flush(inboundCandidate) then
                dropCandidate("candidate-send")
            end
        end

        local conn = connection
        if conn and conn.state == "established" and currentTime - conn.lastRxAt > IDLE_TIMEOUT_MS then
            drop("idle-timeout")
            conn = nil
        end
        if conn and conn.state ~= "established" and currentTime - conn.startedAt > HANDSHAKE_TIMEOUT_MS then
            drop("handshake-timeout")
            conn = nil
        end
        if conn then
            if not finishConnect(conn) then
                drop("connect")
                conn = nil
            elseif conn.state ~= "connecting" and not readConnection(conn) then
                -- Drain any authenticated frames delivered right before TCP EOF/close
                -- before drop() resets per-connection chunk assembly state.
                processEndpointEvents()
                drop("io")
                conn = nil
            end
            conn = connection
        end
        if conn then
            processEndpointEvents()
            if conn.state == "established" then
                if failedApply and currentTime >= failedApply.retryAt then
                    applyOrRetry(failedApply.snapshot)
                end
                if currentTime - lastHeartbeat >= HEARTBEAT_INTERVAL_MS then
                    if queueData(conn, HEARTBEAT_CHANNEL, "ping") then
                        lastHeartbeat = currentTime
                    end
                end
                if pendingSnapshot and currentTime >= pendingSnapshot.retryAt then
                    local pending = pendingSnapshot
                    for _ = 1, 8 do
                        local chunk = pending.chunks[pending.index]
                        if not chunk or not transportApi.send(endpoint, peerId, chunk) then break end
                        pending.index = pending.index + 1
                    end
                    if pending.index > #pending.chunks then
                        pending.index = 1
                        pending.retryAt = currentTime + 1000
                    end
                end
                for _, outMsg in ipairs(transportApi.takeOutbound(adapter, 16)) do
                    if not queueData(conn, outMsg.channel, outMsg.payload) then
                        drop("backpressure")
                        conn = nil
                        break
                    end
                end
            end
        end
        if conn and not flush(conn) then
            drop("send")
        end
        processEndpointEvents()
    end

    function backend.stepOpportunistic(forceStep)
        if stopped then return end
        if not socketsReady then
            if not R._stockInitializedSeen and SLS and SLS.steamEngine == nil then
                return
            end
            local okAct, actErr = backend.activateSockets()
            if not okAct then
                logWarn("RemotePlaySync stock listener activation failed: " .. tostring(actErr))
                return
            end
        end
        local currentTime = nowMs()
        local busy = (connection and connection.state ~= "established")
            or inboundCandidate ~= nil
            or pendingSnapshot ~= nil
        if not forceStep and not busy and (currentTime - lastOpportunisticStepAt) < settings.tickMs then
            return
        end
        lastOpportunisticStepAt = currentTime
        -- During active handshake or chunk transfer on opportunistic CM hooks,
        -- run up to 2 nonblocking passes to drain buffered frames promptly.
        tick()
        if (connection and connection.state ~= "established")
            or inboundCandidate ~= nil
            or (connection and #connection.read >= 4) then
            tick()
        end
    end

    if managed then
        local okAct, actErr = backend.activateSockets()
        if not okAct then
            backend.stop()
            return nil, actErr
        end
        if evidenceEnabled then
            local runTick = tick
            local calls, maximumGap, maximumDuration = 0, 0, 0
            local previous, reportAt = nowMs(), nowMs() + 1000
            tick = function()
                local before = nowMs()
                maximumGap = math.max(maximumGap, before - previous)
                previous = before
                runTick()
                local after = nowMs()
                maximumDuration = math.max(maximumDuration, after - before)
                calls = calls + 1
                if after >= reportAt then
                    local m = type(transportApi.metrics) == "function" and transportApi.metrics() or {}
                    evidence(string.format(
                        "tick tid=%d calls=%d max_gap_ms=%d max_duration_ms=%d peers=%d disconnected=%d rx=%d queued=%d drained=%d rejected=%d event_overflows=%d outbound_overflows=%d applied=%d acked=%d duplicates=%d",
                        threadId(), calls, maximumGap, maximumDuration,
                        m.peersConnected or 0, m.peersDisconnected or 0, m.messagesReceived or 0,
                        m.messagesQueuedToSend or 0, m.messagesTakenToSend or 0, m.messagesRejected or 0,
                        m.eventOverflows or 0, m.outboundOverflows or 0,
                        R.snapshotsApplied or 0, R.snapshotsAcked or 0, R.duplicatesIgnored or 0
                    ))
                    reportAt = after + 1000
                end
            end
        end
        tickHandle = SLS.onTick(tick, settings.tickMs)
        if tickHandle == 0 then
            backend.stop()
            return nil, "tick-registration-failed"
        end
        shutdownHandle = SLS.onShutdown(function(reason)
            evidence("shutdown tid=" .. threadId() .. " reason=" .. tostring(reason))
            stoppingFromShutdown = true
            backend.stop()
            stoppingFromShutdown = false
        end)
        if shutdownHandle == 0 then
            backend.stop()
            return nil, "shutdown-registration-failed"
        end
        backend.tickHandle = tickHandle
    else
        -- Stock SLSsteam mode: only open sockets immediately if SLSsteam::initialized
        -- already ran earlier in this process (e.g., hot reload). During initial
        -- la_objopen, SLS.steamEngine is nil so socket creation waits for initialized.
        if R._stockInitializedSeen or (SLS and SLS.steamEngine ~= nil) then
            R._stockInitializedSeen = true
            local okAct, actErr = backend.activateSockets()
            if not okAct then
                backend.stop()
                return nil, actErr
            end
        end
    end

    backend.transportMetrics = function()
        return type(transportApi.metrics) == "function" and transportApi.metrics() or {}
    end
    return backend
end

-- ============================================================================
-- Local Source Enumeration, Tombstone Tracking, Publish & Snapshot Acceptance
-- ============================================================================

R.generation = R.generation or 0
R.localKey = R.localKey
R.localApps = R.localApps or {}
R.localEntries = R.localEntries or {}
R.tombstones = R.tombstones or {}
R.tombstoneOrder = R.tombstoneOrder or {}
R.remoteLibraries = R.remoteLibraries or {}
R.remoteAdditionalApps = R.remoteAdditionalApps or {}
R.remoteTombstones = R.remoteTombstones or {}
R.remoteTitles = R.remoteTitles or {}
R.peers = R.peers or {}
R.retiredSessions = R.retiredSessions or {}
R.snapshotsPublished = R.snapshotsPublished or 0
R.snapshotsApplied = R.snapshotsApplied or 0
R.snapshotsAcked = R.snapshotsAcked or 0
R.duplicatesIgnored = R.duplicatesIgnored or 0
R.authFailures = R.authFailures or 0
R.framesRejected = R.framesRejected or 0
R.halfOpenReplacements = R.halfOpenReplacements or 0
R.ownershipProtectedCount = R.ownershipProtectedCount or 0
R.lastPublishSucceeded = R.lastPublishSucceeded or false
R.active = false

local backend = nil
local backendKind = "none"
local sourceCache, sourceJob, nextScan = nil, nil, 0

local function refreshStockLocalConfigCache()
    if not SLS or not SLS.config then return {} end
    if not detectManagedApis() and type(SLS.config.getIntList) == "function" then
        local okList, list = pcall(function() return SLS.config:getIntList("AdditionalApps") end)
        if okList and type(list) == "table" then
            R._stockLocalConfigApps = normalizedSet(list)
            return R._stockLocalConfigApps
        end
    end
    if type(SLS.config.getAdditionalApps) == "function" then
        local okApps, apps = pcall(function() return SLS.config:getAdditionalApps() end)
        if okApps and type(apps) == "table" then
            local set = normalizedSet(apps)
            R._stockLocalConfigApps = set
            return set
        end
    end
    return R._stockLocalConfigApps or {}
end

local function readLocalAdditionalApps()
    if detectManagedApis() then
        if SLS and SLS.config and type(SLS.config.getAdditionalApps) == "function" then
            return normalizedSet(SLS.config:getAdditionalApps())
        end
        return {}
    end
    if R._stockLocalConfigApps == nil then
        return refreshStockLocalConfigCache()
    end
    return R._stockLocalConfigApps
end

local function recordTombstone(appId, removedGeneration)
    if not R.tombstones[appId] then
        R.tombstoneOrder[#R.tombstoneOrder + 1] = appId
    end
    R.tombstones[appId] = removedGeneration
    while #R.tombstoneOrder > MAX_TOMBSTONES do
        local oldest = table.remove(R.tombstoneOrder, 1)
        R.tombstones[oldest] = nil
    end
end

local function clearTombstone(appId)
    if not R.tombstones[appId] then return end
    R.tombstones[appId] = nil
    for i = #R.tombstoneOrder, 1, -1 do
        if R.tombstoneOrder[i] == appId then
            table.remove(R.tombstoneOrder, i)
        end
    end
end

local function discoverInstalled()
    if REMOTE_PLAY_SYNC_TEST_MODE and type(REMOTE_PLAY_SYNC_SOURCE) == "function" then
        return REMOTE_PLAY_SYNC_SOURCE()
    end
    return sourceCache, R.sourceReason or "installed-source-pending"
end

local publish

local function advanceSource(now)
    if REMOTE_PLAY_SYNC_TEST_MODE and type(REMOTE_PLAY_SYNC_SOURCE) == "function" then return end
    local root = (backend and backend.settings and backend.settings.steamRoot)
        or os.getenv("SLS_RPS_STEAM_ROOT")
        or ((os.getenv("HOME") or "") .. "/.local/share/Steam")
    if not sourceJob and now >= nextScan then
        nextScan = now + 5000
        local text = readBounded(root .. "/steamapps/libraryfolders.vdf", 2 * 1024 * 1024)
        local value = parseVdf(text)
        local folders = value and value.libraryfolders
        if type(folders) ~= "table" then
            sourceCache = {}
            R.sourceAvailable = false
            R.sourceReason = "libraryfolders-unavailable"
            return
        end
        local jobs, folderCount = {}, 0
        for index, folder in pairs(folders) do
            if type(index) == "string" and index:match("^%d+$") then
                folderCount = folderCount + 1
                if folderCount > 32 or type(folder) ~= "table"
                    or type(folder.path) ~= "string"
                    or folder.path:sub(1, 1) ~= "/"
                    or folder.path:find("%z") then
                    sourceCache = {}
                    R.sourceAvailable = false
                    R.sourceReason = "libraryfolders-unsupported"
                    return
                end
                if type(folder.apps) == "table" then
                    for id in pairs(folder.apps) do
                        local numId = type(id) == "string" and id:match("^%d+$") and tonumber(id) or nil
                        if not numId or not validInteger(numId) or numId > 0xffffffff or #jobs >= MAX_APPS then
                            sourceCache = {}
                            R.sourceAvailable = false
                            R.sourceReason = "manifest-limit"
                            return
                        end
                        jobs[#jobs + 1] = {
                            path = folder.path .. "/steamapps/appmanifest_" .. id .. ".acf",
                            id = numId,
                        }
                    end
                end
            end
        end
        sourceJob = { jobs = jobs, index = 1, entries = {} }
    end
    if not sourceJob then return end
    for _ = 1, 8 do
        local job = sourceJob.jobs[sourceJob.index]
        if not job then
            sourceCache = sourceJob.entries
            sourceJob = nil
            R.sourceAvailable = true
            R.sourceReason = "installed-manifests-ready"
            publish(false)
            return
        end
        sourceJob.index = sourceJob.index + 1
        local text, reason = readBounded(job.path, 65536)
        if text then
            local manifest = parseVdf(text)
            local app = manifest and manifest.AppState
            local flags = app and tonumber(app.StateFlags)
            if app and tonumber(app.appid) == job.id and flags and flags == math.floor(flags)
                and sanitizeTitle(app.name) then
                if math.floor(flags / 4) % 2 == 1 then
                    local prior = sourceJob.entries[job.id]
                    if not prior or app.name < prior.name then
                        sourceJob.entries[job.id] = {
                            appid = job.id,
                            name = app.name,
                            installed = true,
                            ownership = "unknown",
                            streamable = "unknown",
                        }
                    end
                end
            end
        elseif reason ~= "missing" then
            sourceJob = nil
            R.sourceAvailable = false
            R.sourceReason = "manifest-unreadable"
            return
        end
    end
end

local function computeLocalTitles(localApps, installedEntries)
    local titles = {}
    if type(installedEntries) == "table" then
        for appId in pairs(localApps) do
            local entry = installedEntries[appId]
            if entry and sanitizeTitle(entry.name) and entry.name ~= "" then
                titles[appId] = entry.name
            end
        end
    end
    return titles
end

local function computeLocalStateKey(appList, titles, installedEntries)
    local parts = { "A" .. tostring(#appList) }
    for _, appId in ipairs(appList) do
        local title = titles[appId] or ""
        parts[#parts + 1] = tostring(appId) .. ":" .. tostring(#title) .. ":" .. title
    end
    local instIds = {}
    if type(installedEntries) == "table" then
        for appId, entry in pairs(installedEntries) do
            if type(entry) == "table" and entry.installed == true and sanitizeTitle(entry.name) then
                instIds[#instIds + 1] = appId
            end
        end
        table.sort(instIds)
    end
    parts[#parts + 1] = "I" .. tostring(#instIds)
    for _, appId in ipairs(instIds) do
        local name = installedEntries[appId].name
        parts[#parts + 1] = tostring(appId) .. ":" .. tostring(#name) .. ":" .. name
    end
    return table.concat(parts, "|")
end

publish = function(force)
    local localApps = readLocalAdditionalApps()
    local installedEntries = discoverInstalled() or {}
    R.localEntries = installedEntries

    local appList = sortedList(localApps)
    local titles = computeLocalTitles(localApps, installedEntries)
    local key = computeLocalStateKey(appList, titles, installedEntries)
    if not force and key == R.localKey and R.lastPublishSucceeded then
        return true
    end

    if key ~= R.localKey then
        local nextGen = R.generation + 1
        if nextGen > MAX_SAFE_INTEGER then return false end
        -- Update tombstones for any local AdditionalApps removed since previous state
        for oldAppId in pairs(R.localApps or {}) do
            if not localApps[oldAppId] then
                recordTombstone(oldAppId, nextGen)
            end
        end
        for newAppId in pairs(localApps) do
            clearTombstone(newAppId)
        end
        R.generation = nextGen
        R.localKey = key
        R.localApps = localApps
    end

    if not backend then return false end
    local ok
    if backendKind == "test" then
        ok = backend.publish(R.generation, appList, force)
    else
        ok = backend.publish(R.generation, appList, titles, R.tombstones, installedEntries, force)
    end
    R.lastPublishSucceeded = ok
    if ok then
        R.snapshotsPublished = R.snapshotsPublished + 1
        if evidenceEnabled then
            evidence(string.format(
                "queued tid=%d generation=%d apps=%d ids=%s",
                threadId(), R.generation, #appList, evidenceIds(appList)
            ))
        end
    end
    return ok
end

local function acceptSnapshot(snapshot, precomputedKey)
    if type(snapshot) ~= "table"
        or type(snapshot.origin) ~= "string"
        or type(snapshot.appIds) ~= "table" then
        return false
    end
    if not validInteger(snapshot.session) or not validInteger(snapshot.generation) then
        return false
    end

    local previous = R.peers[snapshot.origin]
    if sessionRetired(snapshot.origin, snapshot.session) then
        R.duplicatesIgnored = R.duplicatesIgnored + 1
        return false
    end
    if previous and previous.session == snapshot.session
        and snapshot.generation <= previous.generation then
        R.duplicatesIgnored = R.duplicatesIgnored + 1
        return false
    end

    local apps = normalizedSet(snapshot.appIds)
    local canonical = sortedList(apps)
    if #snapshot.appIds ~= #canonical then
        return false
    end
    for i = 1, #canonical do
        if snapshot.appIds[i] ~= canonical[i] then return false end
    end

    -- Verify tombstones do not overlap active appIds
    if type(snapshot.tombstones) == "table" then
        for tombAppId, removedGen in pairs(snapshot.tombstones) do
            if apps[tombAppId] or not validInteger(removedGen) or removedGen > snapshot.generation then
                return false
            end
        end
    end

    if not backend or not backend.apply(snapshot) then
        return false
    end

    if previous and previous.session ~= snapshot.session then
        retireSession(snapshot.origin, previous.session)
    end

    R.peers[snapshot.origin] = {
        session = snapshot.session,
        generation = snapshot.generation,
        key = setKey(apps),
        contentKey = precomputedKey or snapshotContentKey(snapshot),
    }
    R.snapshotsApplied = R.snapshotsApplied + 1
    if evidenceEnabled then
        evidence(string.format(
            "applied tid=%d origin=%s generation=%d apps=%d installed=%d ids=%s",
            threadId(), snapshot.origin, snapshot.generation,
            #snapshot.appIds, #(snapshot.installedIds or {}), evidenceIds(snapshot.appIds)
        ))
    end
    return true
end

-- ============================================================================
-- Plugin Startup & Stock/Managed Callback Registration
-- ============================================================================

local function runProtected(label, fn)
    local ok, err = xpcall(fn, function(e)
        if debug and type(debug.traceback) == "function" then
            return debug.traceback(tostring(e), 2)
        end
        return tostring(e)
    end)
    if not ok then
        logWarn("RemotePlaySync " .. label .. " error: " .. tostring(err))
    end
end

local function onPeerConnected(_peer)
    publish(true)
end

local function onConfigLoaded()
    runProtected("configLoaded", function()
        evidence("configLoaded tid=" .. threadId())
        refreshStockLocalConfigCache()
        if backend and type(backend.refreshStockEffective) == "function" then
            backend.refreshStockEffective()
        end
        publish(false)
        if backend and type(backend.stepOpportunistic) == "function" then
            backend.stepOpportunistic(true)
        end
    end)
end

local function onInitialized()
    runProtected("initialized", function()
        evidence("initialized tid=" .. threadId())
        R._stockInitializedSeen = true
        refreshStockLocalConfigCache()
        if backend and type(backend.refreshStockEffective) == "function" then
            backend.refreshStockEffective()
        end
        publish(false)
        if backend and type(backend.stepOpportunistic) == "function" then
            backend.stepOpportunistic(true)
        end
        if backend and type(backend.capabilities) == "function" then
            R.capabilities = backend.capabilities()
        end
    end)
end

local function onReload()
    runProtected("luaReload", function()
        evidence("luaReload tid=" .. threadId())
        R.active = false
        if not detectManagedApis() and type(R._stopActiveBackend) == "function" then
            pcall(R._stopActiveBackend, "luaReload")
            R._stopActiveBackend = nil
        end
    end)
end

local function onOpportunisticNetworkPacket()
    runProtected("networkPacket", function()
        if R.active and R.modeTier == "stock-opportunistic" and R._currentBackend
            and type(R._currentBackend.stepOpportunistic) == "function" then
            R._currentBackend.stepOpportunistic(false)
        end
    end)
end

refreshStockLocalConfigCache()

local capabilities = { available = false, transport = "none", tier = "none", reason = "uninitialized" }
if REMOTE_PLAY_SYNC_TEST_MODE and type(REMOTE_PLAY_SYNC_TEST_BACKEND) == "table" then
    backend = REMOTE_PLAY_SYNC_TEST_BACKEND
    backendKind = "test"
    R.modeTier = "test"
    capabilities = backend.capabilities()
else
    local reason
    backend, reason = createPeerBackend({
        onPeerConnected = onPeerConnected,
        onSnapshot = acceptSnapshot,
        reconcile = function() publish(true) end,
        advanceSource = advanceSource,
    })
    if backend then
        backendKind = "peer"
        R.modeTier = backend.tier
        capabilities = backend.capabilities()
        R._stopActiveBackend = function() backend.stop() end
    else
        R.modeTier = "unavailable"
        capabilities = { available = false, transport = "none", tier = "unavailable", reason = reason }
    end
end

R._currentBackend = backend
R._handlers = {
    onConfigLoaded = onConfigLoaded,
    onInitialized = onInitialized,
    onReload = onReload,
    onPacket = onOpportunisticNetworkPacket,
}
R.capabilities = capabilities
R.active = backend ~= nil

-- Register SLS callbacks at most once per lua_State so stock SLSsteam hot-reloads
-- (Lua::init(false) in the same lua_State) never accumulate duplicate callbacks.
if SLS and type(SLS.registerCallback) == "function" and not R.callbacksRegistered then
    SLS.registerCallback("SLSsteam::configLoaded", function()
        if R.active and R._handlers then R._handlers.onConfigLoaded() end
    end)
    SLS.registerCallback("SLSsteam::initialized", function()
        if R.active and R._handlers then R._handlers.onInitialized() end
    end)
    SLS.registerCallback("SLSsteam::luaReload", function()
        if R._handlers then R._handlers.onReload() end
    end)
    if not detectManagedApis() then
        SLS.registerCallback("Network::recvPkt", function(_pkt)
            if R._handlers then R._handlers.onPacket() end
        end)
        SLS.registerCallback("Network::sendPkt", function(_pkt)
            if R._handlers then R._handlers.onPacket() end
        end)
    end
    R.callbacksRegistered = true
end

if not capabilities.available then
    logWarn("RemotePlaySync unavailable: " .. tostring(capabilities.reason))
else
    publish(false)
    logInfo(string.format(
        "RemotePlaySync loaded (tier=%s, transport=%s%s)",
        tostring(capabilities.tier),
        tostring(capabilities.transport),
        (capabilities.reason and capabilities.reason ~= "") and (", note=" .. capabilities.reason) or ""
    ))
    if R._stockInitializedSeen and backend and type(backend.stepOpportunistic) == "function" then
        runProtected("hotReloadStep", function() backend.stepOpportunistic(true) end)
    end
end

if REMOTE_PLAY_SYNC_TEST_MODE then
    R.test = {
        sha256 = sha256,
        hmacSha256 = hmacSha256,
        secureEqual = secureEqual,
        toHex = toHex,
        fromHex = fromHex,
        isAllowedPrivateIPv4 = isAllowedPrivateIPv4,
        parseConfigText = parseConfigText,
        loadConfigFile = loadConfigFile,
        resolveSettings = resolveSettings,
        writePairConfigs = writePairConfigs,
        parseVdf = parseVdf,
        advanceSource = advanceSource,
        discoverInstalled = discoverInstalled,
        encodeSnapshotV3 = encodeSnapshotV3,
        decodeSnapshotV3 = decodeSnapshotV3,
        snapshotContentKey = snapshotContentKey,
        validInteger = validInteger,
        normalizedSet = normalizedSet,
        sortedList = sortedList,
        setKey = setKey,
        publish = publish,
        acceptSnapshot = acceptSnapshot,
        onPeerConnected = onPeerConnected,
        onConfigLoaded = onConfigLoaded,
        onInitialized = onInitialized,
        onPacket = onOpportunisticNetworkPacket,
        stop = function() if backend and backend.stop then backend.stop() end end,
        backend = backend,
        backendKind = backendKind,
    }
end
