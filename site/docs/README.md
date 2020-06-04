# Documentation Site
This directory contains the configuration required to build and deploy the
[documentation site](https://docs.opentitan.org) as well as the continuous
deployment configuration that pushes a rebuilt copy of the documentation after
every commit.

# Documentation Builder
In order to speed up the deployment there is a GCR image
(`gcr.io/active-premise-257318/builder`) that contains all of the project's
python requirements pre-installed.  This cuts the deployment from several
minutes to around twenty seconds.  To rebuild and deploy the image use the
`deploy-builder.sh` script.

# Update Hugo version

The Hugo version is defined by variable `HUGO_EXTENDED_VERSION` in `util/build_docs.py`.
To ensure syntax highlighting is working correctly the CSS stylesheet must be updated following a version update.

## Update CSS stylesheet

Setting the option `noClasses = false` for `[markup.highlight]` in `site/docs/config.toml` requires a stylesheet to be available.
This option is used in order to have two styles for light and dark mode of the documentation site.
The stylesheet is stored in `site/docs/assets/scss/_chroma.scss`.
Update the style if the Hugo version is changed:

- Replace the content of `[data-user-color-scheme='light']` with the output of `hugo gen chromastyles --style=colorful`, but keep the first line containing the setting of the background.

- Replace the content of `[data-user-color-scheme='dark']` with the output of `hugo gen chromastyles --style=dracula`, but keep the first line containing the setting of the background.
