# Site Infrastructure
This directory contains the scripts and configuration required to update the [opentitan.org][ot] public-facing website.

# Dependencies
These scripts require that you have [hugo][install-hugo] and [gcloud][install-gcloud] installed and that your gcloud is configured with the correct GCP project.
The production site project can be selected with:

```
gcloud config set project gold-hybrid-255313
```

# Serving Locally
To serve the site locally run the `serve.sh` script, which will build and serve the site on [localhost:1313](http://localhost:1313), automatically rebuilding pages when they are changed.

# Deploying
To deploy the site use the `deploy.sh` script.
Specify the environment (either `public` or `staging`) as the first argument to choose between the two environments.
The script takes care of flushing the CDN cache to make sure changes are visible as quickly as possible.

[install-gcloud]: https://cloud.google.com/sdk/install
[install-hugo]: https://github.com/gohugoio/hugo#choose-how-to-install
[ot]: https://opentitan.org
