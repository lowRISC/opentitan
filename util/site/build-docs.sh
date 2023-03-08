#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# Get the project directory from the location of this script
this_dir=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
proj_root=$( realpath "${this_dir}/../.." )
build_dir="${proj_root}/build-site"

#######
# CLI #
#######
declare command="build"
# The following are only used for "command='serve-proxy'" ------------------------|
declare public_domain="" # (optional) The public-facing domain                  <-|
declare public_port=""   # (optional)The port added to the public-facing domain <-|

case "$1" in
  "build"|"build-local"|"build-staging"|"serve"|"serve-proxy")
    command="$1"
    public_domain="${2}"
    public_port="${3}"
    ;;
  "help"|*)
    echo "USAGE: $0 <command> [public_domain] [public_port]"
    echo ""
    echo "commands:"
    echo "  help          prints this message."
    echo "  build         build the site and docs for prod"
    echo "  build-local   build the site and docs for a localhost server"
    echo "  build-staging build the site and docs for staging.opentitan.org"
    echo "  serve         build and serve the site locally"
    echo "  serve-proxy   build and serve the site, with a public url"
    echo ""
    echo "Optional arguments [public_domain] and [public_port] are only used when command='serve-proxy'"
    exit 0
    ;;
esac

################
# DEPENDENCIES #
################

checkDeps () {
    # Check for mdbook dep
    if ! command -v mdbook >/dev/null; then
        echo "E: mdbook not found, please install from your package manager or with:" >&2
        echo "E:   $ cargo install mdbook" >&2
        exit 1
    fi

    # Check for hugo dep
    if ! command -v hugo >/dev/null; then
        echo "E: hugo not found, please install from your package manager" >&2
        exit 1
    fi
}
checkDeps

#################
# CONFIGURATION #
#################
declare base_url
declare serve_port # The port used by the local webserver (using "build-docs.sh serve/serve-proxy")

getURLs () {
    # Defaults here are for production ("build-docs.sh build")
    local scheme="https"
    local domain="opentitan.org"
    local port=""

    # Use un-encrypted localhost URLs when building/serving locally
    # - serve on port 9000.
    if [ "$command" = "build-local" ] || \
       [ "$command" = "serve" ]; then
        scheme="http"
        domain="localhost"
        port=":9000"
        serve_port=":9000"
    fi
    # "serve-proxy" gives us some simple defaults for serving behind a proxy:
    # - set the public_domain/public_port appropriately (see $2/$3)
    # - serve on port 8000.
    if [ "$command" = "serve-proxy" ] ; then
        scheme="http"
        domain="${public_domain}"
        port=":${public_port}"
        serve_port=":8000"
    fi
    if [ "$command" = "build-staging" ] ; then
        scheme="https"
        domain="staging.opentitan.org"
    fi

    base_url="${scheme}://${domain}${port}"
}
getURLs

# Export some environment variables that tools will pick up
export HUGO_PARAMS_DOCSURL="${base_url}/book" # hugo
export URL_ROOT="${base_url}/book" # earlgrey_diagram

# Build up doxygen command
doxygen_env="env"
doxygen_env+=" SRCTREE_TOP=${proj_root}"
doxygen_env+=" DOXYGEN_OUT=${build_dir}/gen"
doxygen_args="${proj_root}/util/doxygen/Doxyfile"

# Build up mdbook arguments
mdbook_args="build"
mdbook_args+=" --dest-dir ${build_dir}/book/"
mdbook_args+=" ${proj_root}"

mdbook_guides_args="build"
mdbook_guides_args+=" --dest-dir ${build_dir}/guides/getting_started"
mdbook_guides_args+=" ${proj_root}/doc/guides/getting_started"

# Register the pre-processors
# Each book should only be passed the preprocessors it specifies inside the book.toml
# ./book.toml
book_env="env"
book_env+=" MDBOOK_PREPROCESSOR__TESTPLAN__COMMAND=${proj_root}/util/mdbook_testplan.py"
book_env+=" MDBOOK_PREPROCESSOR__OTBN__COMMAND=${proj_root}/util/mdbook_otbn.py"
book_env+=" MDBOOK_PREPROCESSOR__DOXYGEN__COMMAND=${proj_root}/util/mdbook_doxygen.py"
book_env+=" MDBOOK_PREPROCESSOR__REGGEN__COMMAND=${proj_root}/util/mdbook_reggen.py"
book_env+=" MDBOOK_PREPROCESSOR__WAVEJSON__COMMAND=${proj_root}/util/mdbook_wavejson.py"
book_env+=" MDBOOK_PREPROCESSOR__README2INDEX__COMMAND=${proj_root}/util/mdbook_readme2index.py"
book_env+=" MDBOOK_PREPROCESSOR__DASHBOARD__COMMAND=${proj_root}/util/mdbook_dashboard.py"
# ./doc/guides/getting_started/book.toml
book_guides_env="env"
book_guides_env+=" MDBOOK_PREPROCESSOR__TOOLVERSION__COMMAND=${proj_root}/util/mdbook_toolversion.py"
book_guides_env+=" MDBOOK_PREPROCESSOR__README2INDEX__COMMAND=${proj_root}/util/mdbook_readme2index.py"

# Build up Hugo arguments
hugo_args=""
hugo_args+=" --source ${proj_root}/site/landing/"
hugo_args+=" --destination ${build_dir}/"
hugo_args+=" --baseURL ${base_url}"

############
# BUILDING #
############

buildSite () {
    mkdir -p "${build_dir}"
    mkdir -p "${build_dir}/gen/doxy"

    echo "Building doxygen..."
    pushd "${this_dir}" >/dev/null
    # shellcheck disable=SC2086
    ${doxygen_env} doxygen ${doxygen_args}
    popd >/dev/null
    echo "Doxygen build complete."

    # shellcheck disable=SC2086
    ${book_env} mdbook ${mdbook_args}
    # shellcheck disable=SC2086
    ${book_guides_env} mdbook ${mdbook_guides_args}
    # shellcheck disable=SC2086
    hugo ${hugo_args}
}
buildSite

###########
# SERVING #
###########

# If serving, run the python HTTP server
if [ "$command" = "serve" ] || [ "$command" = "serve-proxy" ]; then
  echo "--------------------------------------------"
  echo
  echo "Website being served at : ${base_url}"
  echo
  echo "--------------------------------------------"
  python3 -m http.server -d "$build_dir" ${serve_port:1}
                                         # strip leading :
fi
