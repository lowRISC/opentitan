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
export URL_ROOT="${base_url}/book" # earlgrey_diagram

# Build up doxygen command
doxygen_env="env"
doxygen_env+=" SRCTREE_TOP=${proj_root}"
doxygen_env+=" DOXYGEN_OUT=${build_dir}/gen"
doxygen_args="${proj_root}/util/doxygen/Doxyfile"

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
book_env+=" MDBOOK_PREPROCESSOR__BLOCK_DASHBOARD__COMMAND=${proj_root}/util/mdbook-block-dashboard.py"
book_env+=" MDBOOK_OUTPUT__HTML__THEME=$proj_root/site/book-theme/"
book_env+=" MDBOOK_OUTPUT__HTML__DEFAULT_THEME=unicorn-vomit-light"
book_env+=" MDBOOK_OUTPUT__HTML__PREFERRED_DARK_THEME=unicorn-vomit-light"
book_args="build"
book_args+=" --dest-dir ${build_dir}/book/"
book_args+=" ${proj_root}"
# ./doc/guides/getting_started/book.toml
gettingstarted_book_env="env"
gettingstarted_book_env+=" MDBOOK_PREPROCESSOR__TOOLVERSION__COMMAND=${proj_root}/util/mdbook_toolversion.py"
gettingstarted_book_env+=" MDBOOK_PREPROCESSOR__README2INDEX__COMMAND=${proj_root}/util/mdbook_readme2index.py"
gettingstarted_book_env+=" MDBOOK_OUTPUT__HTML__THEME=$proj_root/site/book-theme/"
gettingstarted_book_env+=" MDBOOK_OUTPUT__HTML__DEFAULT_THEME=unicorn-vomit-light"
gettingstarted_book_env+=" MDBOOK_OUTPUT__HTML__PREFERRED_DARK_THEME=unicorn-vomit-light"
gettingstarted_book_args="build"
gettingstarted_book_args+=" --dest-dir ${build_dir}/guides/getting_started"
gettingstarted_book_args+=" ${proj_root}/doc/guides/getting_started"

# Build up Hugo arguments
hugo_args=""
hugo_args+=" --source ${proj_root}/site/landing/"
hugo_args+=" --destination ${build_dir}/"
hugo_args+=" --baseURL ${base_url}"

############
# BUILDING #
############

buildSite () {
    echo "Build Directory : ${build_dir}"
    mkdir -p "${build_dir}"
    mkdir -p "${build_dir}/gen/doxy"

    echo "Building doxygen..."
    pushd "${this_dir}" >/dev/null
    # shellcheck disable=SC2086
    ${doxygen_env} doxygen ${doxygen_args}
    popd >/dev/null
    echo "Doxygen build complete."

    # shellcheck disable=SC2086
    ${book_env} ./bazelisk.sh run --experimental_convenience_symlinks=ignore @crate_index//:mdbook__mdbook -- ${book_args}
    # shellcheck disable=SC2086
    ${gettingstarted_book_env} ./bazelisk.sh run --experimental_convenience_symlinks=ignore @crate_index//:mdbook__mdbook -- ${gettingstarted_book_args}
    # shellcheck disable=SC2086
    hugo ${hugo_args}

    # Build Rust Documentation
    local rustdoc_dir="${build_dir}/gen/rustdoc/"
    mkdir -p "${rustdoc_dir}"
    local bazel_out target_rustdoc target_rustdoc_output_path
    bazel_out="$(./bazelisk.sh info output_path 2>/dev/null)"
    target_rustdoc="sw/host/opentitanlib:opentitanlib_doc"
    target_rustdoc_output_path="${bazel_out}/k8-fastbuild/bin/$(echo ${target_rustdoc} | tr ':' '/').rustdoc" #TODO : get the target's path using cquery
    ./bazelisk.sh build --experimental_convenience_symlinks=ignore "${target_rustdoc}"
    cp -rf "${target_rustdoc_output_path}"/* "${rustdoc_dir}"
    # The files from bazel-out aren't writable. This ensures those that were copied are.
    chmod +w -R "${rustdoc_dir}"

    # Block diagram stats
    mkdir -p "${build_dir}/reports"
    python3 "${proj_root}/util/site/fetch_block_stats.py" "${build_dir}/reports/earlgrey-stats.json"

    # CLEANUP
    # Remove (larger) files from the ${build_dir} that do not need to be deployed
    # -------
    # Remove some unneeded files/directories that mdbook copies to the output dir
    # TODO handle this with a .ignore file or other mechanism
    for f in .git .github build-site site; do
        rm -rf "${build_dir}/book/${f}"
    done
    rm -rf "${build_dir}/gen/api-xml" # Remove the intermediate XML that doxygen uses to generate HTML.
    rm -rf "${build_dir}/book/sw/vendor/wycheproof/testvectors"
    # -------
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
