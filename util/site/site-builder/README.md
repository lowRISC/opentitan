# Site-Builder Container

`builder.Dockerfile` defines a container with all of the required dependencies to build the site + documentation.
In order to speed up the deployment, an image of this container is deployed to the Google Container Registry (GCR) (`gcr.io/gold-hybrid-255313/builder`).
This image is used to spawn a Gcloud 'Cloud Build' job whenever a PR is merged into master, which runs the steps in `cloudbuild-deploy-docs.yaml`.
After running the site build script (`util/site/build-docs.sh`), this job copies the generated artifacts to the Gcloud bucket which serves the website.
This cuts the deployment of any updated site/documentation changes down to about 1 minute.
