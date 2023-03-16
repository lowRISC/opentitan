# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:22.10

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    fonts-freefont-ttf locales locales-all \
    git curl \
    doxygen hugo xsltproc \
    python3 python3-pip \
    gcc libc-dev

ENV LC_ALL "en_US.UTF-8"
ENV LANG "en_US.UTF-8"
ENV LANGUAGE en_US:en

RUN mkdir -p /tools

##############
### nodejs ###
##############

# Install nodejs
ENV NODE_VERSION "v18.15.0"
ENV NVM_DIR "/tools/.nvm"
ENV PATH "/tools/.nvm/versions/node/${NODE_VERSION}/bin:${PATH}"
RUN mkdir /tools/.nvm \
    && curl -so- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.1/install.sh | bash \
    && . "/tools/.nvm/nvm.sh" \
    && nvm install "${NODE_VERSION}"

# Install chrome-unstable for puppeteer
RUN curl -so/tmp/chrome.deb https://dl.google.com/linux/direct/google-chrome-unstable_current_amd64.deb \
    && apt-get install -y --no-install-recommends /tmp/chrome.deb

# Create and prepopulate npm and puppeteer caches
ENV PUPPETEER_CACHE_DIR "/tools/.puppeteer"
ENV npm_config_cache "/tools/.npm"
COPY site/earlgrey-diagram/package*.json /tmp/site/earlgrey-diagram/
RUN npm --prefix /tmp/site/earlgrey-diagram/ install

############
### rust ###
############

# Install cargo and mdbook
ENV RUSTUP_HOME "/tools/.rustup"
ENV CARGO_HOME "/tools/.cargo"
ENV PATH "/tools/.cargo/bin:${PATH}"
RUN curl -so- https://sh.rustup.rs | bash -s -- -y \
    && cargo install mdbook

##############
### python ###
##############

# Explicitly updating pip and setuptools is required to have these tools
# properly parse Python-version metadata, which some packages uses to
# specify that an older version of a package must be used for a certain
# Python version. If that information is not read, pip installs the latest
# version, which then fails to run.
COPY python-requirements.txt ./
ENV PATH "/root/.local/bin:${PATH}"
RUN python3 -m pip install -U pip "setuptools<66.0.0" \
  && pip3 install -r python-requirements.txt



# Make /tools accessible to everyone
RUN chmod -R a+rwX /tools
# Cleanup
RUN apt-get clean; rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /usr/share/doc/*
