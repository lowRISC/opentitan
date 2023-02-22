# Appendix

## Update CSS stylesheet

Setting the option `noClasses = false` for `[markup.highlight]` in `site/landing/config.toml` requires a stylesheet to be available.
This option is used in order to have two styles for light and dark mode of the documentation site.
The stylesheet is stored in `site/landing/assets/scss/_chroma.scss`.
Update the style if the Hugo version is changed:

- Replace the content of `[data-user-color-scheme='light']` with the output of `hugo gen chromastyles --style=colorful`, but keep the first line containing the setting of the background.

- Replace the content of `[data-user-color-scheme='dark']` with the output of `hugo gen chromastyles --style=dracula`, but keep the first line containing the setting of the background.
