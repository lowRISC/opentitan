#!/usr/bin/env bash

set -e

command="build"

case "$1" in
  "build"|"build-local"|"serve"|"serve-proxy")
    command="$1"
    public_url="${2}"
    public_port="${3}"
    ;;
  "help"|*)
    echo "USAGE: $0 [command]"
    echo ""
    echo "commands:"
    echo "  help         prints this message."
    echo "  build        build the site and docs for prod"
    echo "  build-local  build the site and docs for a localhost server"
    echo "  serve        build and serve the site locally"
    echo "  serve-proxy  build and serve the site, with a public url"
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
declare docs_url
declare serve_port
declare public_port

# Get the project directory from the location of this script
this_dir=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
proj_root=$(realpath "${this_dir}/../..")

# Create the output directory
build_dir="$proj_root/build-site"
mkdir -p "$build_dir"

getURLs () {
    # Default urls here are for production
    local base_stem="https://opentitan.org"

    # Use localhost for URL's when building/serving locally
    if [ "$command" = "build-local" ] || \
       [ "$command" = "serve" ]; then
        base_stem="http://localhost"
        serve_port=":9000"
        public_port=":9000"
    fi
    # If the site is behind a proxy, set the URL/public_port appropriately
    if [ "$command" = "serve-proxy" ] ; then
        base_stem="http://${public_url}"
        serve_port=":8000"
        public_port=":${public_port}"
    fi

    base_url="${base_stem}${public_port}"
    docs_url="${base_stem}${public_port}/book"
}
getURLs

# Export some environment variables that tools will pick up
export HUGO_PARAMS_DOCSURL="${docs_url}" # hugo
export URL_ROOT="${docs_url}" # earlgrey_diagram

# Build up doxygen command
doxygen_env="env"
doxygen_env+=" SRCTREE_TOP=${proj_root}"
doxygen_env+=" DOXYGEN_OUT=${build_dir}/gen"
doxygen_args="${proj_root}/util/doxygen/Doxyfile"
mkdir -p "${build_dir}/gen/doxy"

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

# Build up Hugo arguments
hugo_args=""
hugo_args+=" --source ${proj_root}/site/landing/"
hugo_args+=" --destination ${build_dir}/"
hugo_args+=" --baseURL ${base_url}"

############
# BUILDING #
############

buildSite () {
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
