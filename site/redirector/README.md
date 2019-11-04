# `redirector`
The redirector container is a minimal nginx deployment that is responsible for upgrading HTTP connections to HTTPS via a redirect and for redirecting requests to the top-level domain if they arrive on a subdomain (like www).

# Deploying
To rebuild and deploy the redirector instance group use the `deploy.sh` script.
Note that it can take a while for the instance group to catch up with the update, and then up to twelve hours for the CDN cache to expire.
We cannot invalidate the CDN immediately after issuing the rolling-update request to the instance group because the operation will take time to complete.

If you need to do a faster push: wait until the rolling restart is complete and manually invalidate the CDN.
