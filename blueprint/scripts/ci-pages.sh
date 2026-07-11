#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "$0")/.."

lake build ProetaleBlueprint
lake env lean --run ProetaleBlueprintMain.lean --output _out/site

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
