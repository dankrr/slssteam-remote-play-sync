# SLSsteam Remote Play Sync

A Lua plugin that synchronizes SLSsteam game entries between Linux PCs and Steam Decks using Steam Remote Play.

## Features

- Bidirectional synchronization of SLSsteam game entries
- Makes synchronized games available for Remote Play streaming
- Supports game additions and removals
- Uses the existing Steam Remote Play connection
- No separate server required

Synchronizes library entries, not installed game files or saves.

## Requirements

- Linux Steam (64-bit)
- SLSsteam with compatible Lua plugin and synchronization APIs
- Steam Remote Play enabled on both devices

Compatibility with stock SLSsteam builds is not guaranteed.

## Installation

Install on **both devices**.

1. Download `remote_play_sync.lua`.
2. Copy it to `~/.config/SLSsteam/plugins/`.
3. Enable `Plugins: yes` in `~/.config/SLSsteam/config.yaml`.
4. Fully restart Steam on both devices.

## Updating

Replace the Lua file and restart Steam.

## Uninstalling

Close Steam, remove `remote_play_sync.lua` from the plugins directory, and restart Steam.

## Disclaimer

Independent community plugin. Not affiliated with Valve or SLSsteam.
