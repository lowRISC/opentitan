#!/usr/bin/env bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

#######
# CLI #
#######

command=""
# The following are only used for `serve-proxy`
public_domain="" # (optional) The public-facing domain
public_port=""   # (optional) The port added to the public-facing domain

case "$1" in
  "build"|"build-local"|"build-staging"|"serve")
    command="$1"
    ;;
  "serve-proxy")
    command="$1"
    public_domain="$2" # Optional
    public_port="$3"   # Optional
    ;;
  "help"|*)
    echo "USAGE: $0 <command> [args...]"
    echo ""
    echo "commands:"
    echo "  help          prints this message."
    echo "  build         build the site and docs for prod"
    echo "  build-local   build the site and docs for a localhost server"
    echo "  build-staging build the site and docs for staging.opentitan.org"
    echo "  serve         build and serve the site locally"
    echo "  serve-proxy [PUBLIC_DOMAIN] [PUBLIC_PORT]"
    echo "                build and serve the site with a public url"
    exit 0
    ;;
esac

################
# DEPENDENCIES #
################

# Check for node (optional)
if command -v npm >/dev/null && node --version 2>&1 | grep -E '^v(1[4-9]|2[0-9])\.' > /dev/null 2>&1; then
    HAS_NODE=1
else
    HAS_NODE=0
    echo "W: npm or node^14.0 not found - block diagram will not be built" >&2
    echo "W: You can install with nvm:" >&2
    echo "W:    $ curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.3/install.sh | bash" >&2
    echo "W:    $ source ~/.bashrc" >&2
    echo "W:    $ nvm install -lts" >&2
fi

# Check for doxygen
if ! command -v doxygen >/dev/null; then
    echo "E: doxygen not found, please install from your package manager" >&2
    exit 1
fi

# Check for mdbook
if ! command -v mdbook >/dev/null; then
    echo "E: mdbook not found, please install from your package manager or with:" >&2
    echo "E:   $ cargo install mdbook" >&2
    exit 1
fi

# Check for hugo
if ! command -v hugo >/dev/null; then
    echo "E: hugo not found, please install from your package manager" >&2
    exit 1
fi

#################
# CONFIGURATION #
#################

### Directories

this_dir=$(cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd)
proj_root=$(realpath "${this_dir}/../..")
build_dir="${proj_root}/build-site"

### URLs

# Default prod URL
base_url="https://opentitan.org:9000"

case "$command" in
  "build-local"|"serve")
    # Use un-encrypted localhost URLs when building/serving locally
    base_url="http://localhost:9000"
    ;;
  "serve-proxy")
    base_url="http://${public_domain}:${public_port}"
    ;;
  "build-staging")
    base_url="https://staging.opentitan.org"
    ;;
esac

### Settings via environment variables

### Doxygen
export SRCTREE_TOP="${proj_root}"
export DOXYGEN_OUT="${build_dir}/gen"
# mdbook theme
export MDBOOK_OUTPUT__HTML__THEME="$proj_root/site/book-theme/"
# Hugo
export HUGO_PARAMS_DOCSURL="${base_url}/book"
# Block diagram
export URL_ROOT="${base_url}/book"

############
# BUILDING #
############

mkdir -p "${build_dir}"
mkdir -p "${build_dir}/gen/doxy"

# Build earlgrey-diagram if node is available
if [ "$HAS_NODE" == "1" ]; then
    echo "Building earlgrey diagram..."
    npm --prefix "${proj_root}/site/earlgrey-diagram" install
    npm --prefix "${proj_root}/site/earlgrey-diagram" run build
    npm --prefix "${proj_root}/site/earlgrey-diagram" run deploy
    echo "Earlgrey diagram build complete."
fi

echo "Running doxygen - this may take a while..."

pushd "$this_dir" >/dev/null
doxygen "${proj_root}/util/doxygen/Doxyfile"
popd >/dev/null

echo "Doxygen build complete"

pushd "$proj_root" >/dev/null
mdbook build --dest-dir "${build_dir}/book/"
popd >/dev/null

pushd "${proj_root}/doc/guides/getting_started" >/dev/null
mdbook build --dest-dir "${build_dir}/guides/getting_started"
popd >/dev/null

echo "Building landing site..."
pushd "${proj_root}/site/landing" >/dev/null
hugo --destination "${build_dir}/" --baseURL "$base_url"
popd >/dev/null
echo "Finished building site"

###########
# SERVING #
###########

# If serving, run the python HTTP server
if [ "$command" = "serve" ] || [ "$command" = "serve-proxy" ]; then
    # The port used by the local webserver (using "build-docs.sh serve/serve-proxy")
    serve_port="9000"
    if [ "$command" = "serve-proxy" ]; then
        serve_port="8000"
    fi

    python3 -m http.server -d "$build_dir" "$serve_port"
fi
