"""Builds the single-file page: inlines the WebAssembly module into page.html.

Usage: python3 assemble.py MODULE.wasm page.html OUTPUT.html
"""
import base64
import sys

module, template, output = sys.argv[1:4]
with open(module, "rb") as f:
    encoded = base64.b64encode(f.read()).decode("ascii")
with open(template, encoding="utf-8") as f:
    page = f.read()
if page.count("__WASM_BASE64__") != 1:
    sys.exit("the template must contain the placeholder exactly once")
with open(output, "w", encoding="utf-8") as f:
    f.write(page.replace("__WASM_BASE64__", encoded))
print(f"{output}: {len(page) + len(encoded) - len('__WASM_BASE64__')} bytes")
