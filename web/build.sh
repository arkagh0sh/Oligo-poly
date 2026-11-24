#!/bin/sh
# Builds web/dist/index.html: one HTML file with the WebAssembly module inside.
# It opens in a browser directly from the disk, or from any web server.
set -eu
cd "$(dirname "$0")"
cargo build --release --target wasm32-unknown-unknown --lib
mkdir -p dist
python3 assemble.py target/wasm32-unknown-unknown/release/oligo_poly_web.wasm page.html dist/index.html
