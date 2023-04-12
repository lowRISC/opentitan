#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
##########################################################
#
# Script to automate site deployment tasks to Gcloud
#
# You will require authentication to perform Gcloud actions
# against the project id's specified.
# If you have been granted appropriate permissions, you can
# authenticate locally by running `gcloud auth login`, and
# after that the commands here should execute as-intended.
#
##########################################################

set -e

# Get the project directory from the location of this script
this_dir=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
proj_root=$( realpath "${this_dir}/../.." )
build_dir="${proj_root}/build-site"

declare PROJECT           # Gcloud project
declare INSTANCE_GROUP    # Gcloud compute instance group

# docs.opentitan.org
DOCS_OPENTITAN_ORG_ID=active-premise-257318

# opentitan.org
OPENTITAN_ORG_ID=gold-hybrid-255313

################
# DEPENDENCIES #
################

# Check for gcloud-sdk
if ! command -v gcloud >/dev/null; then
    echo "E: gcloud not found." >&2
    echo "E: See instructions at https://cloud.google.com/sdk/docs/install, or:" >&2
    echo "E:   $ nix shell nixpkgs#google-cloud-sdk" >&2
    exit 1
fi

# Check for podman
if ! command -v podman >/dev/null; then
    echo "E: podman not found." >&2
    echo "E: See instructions at https://podman.io/getting-started/installation" >&2
    exit 1
fi

#################
# CONFIGURATION #
#################

############
# BUILDING #
############

deploy_redirector () {
    # site/redirector/landing
    # "Build and deploy a new container image which is used to spawn Gcloud instances that handle redirects"
    #
    #   Note that it can take a while for the instance group to catch up with the update, and then up to twelve hours for the CDN cache to expire.
    #   If you need to do a faster push: wait until the rolling restart is complete and manually invalidate the CDN.
    #
    PROJECT="${OPENTITAN_ORG_ID}"
    INSTANCE_GROUP=opentitan-dot-org-redirector
    gcloud config set project ${PROJECT}
    gcloud builds submit --tag "gcr.io/${PROJECT}/redirector_v2" "${proj_root}/site/redirector/landing"
    gcloud compute instance-groups managed rolling-action replace --max-surge=3 --region=us-central1 "${INSTANCE_GROUP}"
}

deploy_docs_redirector () {
    # site/redirector/docs
    # Redirector but for the DOCS_OPENTITAN_ORG_ID project
    PROJECT="${DOCS_OPENTITAN_ORG_ID}"
    INSTANCE_GROUP=docs-redirector
    gcloud config set project ${PROJECT}
    gcloud builds submit --tag "gcr.io/${PROJECT}/redirector_v2" "${proj_root}/site/redirector/docs"
    gcloud compute instance-groups managed rolling-action replace --max-surge=3 --region=us-central1 "${INSTANCE_GROUP}"
}

deploy_site_builder () {
    # util/site/site-builder
    # "Build and deploy a new container image which is used by a Gcloud 'Cloud Build' job to automatically rebuild the site upon PRs being merged."
    PROJECT="${OPENTITAN_ORG_ID}"
    gcloud config set project ${PROJECT}
    # Build the image locally using podman for speed
    tag="gcr.io/${PROJECT}/builder" # https://cloud.google.com/container-registry/docs/pushing-and-pulling#tag
    pushd ${proj_root}
    podman build -t "${tag}" -f "${proj_root}/util/site/site-builder/builder.Dockerfile" .
    popd
    gcloud auth print-access-token | podman login -u oauth2accesstoken --password-stdin gcr.io && \
        podman push "${tag}"
}

deploy_staging () {
    # "Build the site for staging and deploy it to the staging bucket hosted at staging.opentitan.org"
    PROJECT="${OPENTITAN_ORG_ID}"
    rm -rf ${build_dir}
    ${proj_root}/util/site/build-docs.sh build-staging
    remove_cruft
    gcloud storage cp -R --gzip-in-flight-all ${build_dir}/* gs://${PROJECT}-staging
}

deploy_prod () {
    # DO_NOT_USE
    # "Build the site for production and deploy it to the production bucket hosted at opentitan.org"
    PROJECT="${OPENTITAN_ORG_ID}"
    rm -rf ${build_dir}
    ${proj_root}/util/site/build-docs.sh build
    remove_cruft
    gcloud storage cp -R --gzip-in-flight-all ${build_dir}/* gs://${PROJECT}-prod
}

# Remove additional files from build directory that we don't need
# TODO remove this when we are ready for .mdbookignore (https://github.com/rust-lang/mdBook/pull/1908)
remove_cruft () { rm -rf ${build_dir}/book/.git ${build_dir}/book/.github ${build_dir}/book/build-site ${build_dir}/book/site ; }

#######
# CLI #
#######
case "$1" in
    "redirector") deploy_redirector ;;
    "redirector-docs") deploy_docs_redirector ;;
    "site-builder") deploy_site_builder ;;
    "staging") deploy_staging ;;
    "prod") deploy_prod ;; # DO NOT USE
    "help"|*)
        echo "USAGE: $0 <command>"
        echo ""
        echo "commands:"
        echo "  help             prints this message."
        echo "  site-builder     build and deploy the site-builder container image"
        echo "  staging          build and deploy the site to staging.opentitan.org"
        echo "  redirector       build and deploy the redirector instances for production"
        echo "  redirector-docs  build and deploy the redirector instances for docs.opentitan.org"
        exit 0
        ;;
esac
