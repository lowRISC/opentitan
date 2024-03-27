# Host Manufacturing ECC Keys

Host manufacturing ECC keys are used to
1. generate a shared AES key for exporting the RMA unlock token during device personalization, and
1. endorse the UDS attestation TBS certificate.
The fake keys stored here are used for testing purposes only (see the `personalize_functest` in `sw/device/silicon_creator/manuf/lib/`).
These fake keys have been generated using OpenSSL, and the private portion of the key has been checked into the repository.
Tests can reference this key file, and use it to derive the associated public key on the fly.

# Generating Additional Keys with OpenSSL

To generate additional fake keys for testing using OpenSSL, follow these steps:
```sh
# Generate the curve:
$ openssl ecparam -out curve.pem -name prime256v1

# Generate the ECC private key:
$ openssl ecparam -in curve.pem -genkey -out sk.pem

# Convert the ECC private key from SEC1 format to PKCS8 (we do this because
# the Rust elliptic-curve crate is able to load PKCS8 keys with less additional
# crates):
$ openssl pkcs8 -in sk.pem -topk8 -nocrypt -out sk.pkcs8.der -outform DER

# Show the ECC public key (not required, but helps confirm the above worked):
$ openssl ec -in sk.pem -text -noout
```

To generate a Root CA certificate using the earlier generated private EC key:
```sh
# Create a CSR (Certificate Signing Request) configuration file
# with the following contents:
$ cat fake_ca.conf
[req]
default_bits = 2048
prompt = no
default_md = sha256
distinguished_name = dn
x509_extensions = v3_ca

[dn]
C=US
ST=CA
L=San Jose
O=Google
OU=Engineering
CN=OT Fake CA certificate

[v3_ca]
subjectKeyIdentifier = hash
authorityKeyIdentifier = keyid:always,issuer:always
basicConstraints = critical,CA:true
keyUsage = digitalSignature, keyCertSign, cRLSign

# Generate the CSR:
$ openssl req -new -key sk.pem -out fake_ca.csr -config fake_ca.conf
# Create the certificate:
$ openssl x509 -req -in fake_ca.csr -signkey sk.pem \
       -out fake_ca.pem -days 3650 -extfile fake_ca.conf \
       -extensions v3_ca
Signature ok
subject=C = US, ST = CA, L = San Jose, O = Google, OU = Engineering, CN = OT Fake CA certificate
Getting Private key
$
```

To examine the generated certificate run
```sh
$ openssl x509 -in fake_ca.pem -text
Certificate:
    Data:
        Version: 3 (0x2)
        Serial Number:
            1a:8f:86:2b:3c:75:83:2b:b2:ff:2b:7b:13:81:7a:70:20:ac:0a:62
        Signature Algorithm: ecdsa-with-SHA256
        Issuer: C = US, ST = CA, L = San Jose, O = Google, OU = Engineering, CN = OT Fake CA certificate
        Validity
            Not Before: Apr  2 01:06:42 2024 GMT
            Not After : Mar 31 01:06:42 2034 GMT
        Subject: C = US, ST = CA, L = San Jose, O = Google, OU = Engineering, CN = OT Fake CA certificate
        Subject Public Key Info:
            Public Key Algorithm: id-ecPublicKey
                Public-Key: (256 bit)
                pub:
                    04:1d:05:5a:45:e5:92:3c:ea:e5:04:7a:74:f6:c8:
                    8c:0c:22:74:16:15:18:b5:df:9d:7c:5e:f8:0e:42:
                    a5:77:e0:0c:3c:1a:b2:43:78:89:96:b4:aa:7f:f6:
                    62:86:7e:dd:a1:bb:bb:62:01:f2:d6:99:56:83:be:
                    51:11:61:70:91
                ASN1 OID: prime256v1
                NIST CURVE: P-256
        X509v3 extensions:
            X509v3 Subject Key Identifier:
                46:26:E1:CC:8E:40:91:32:31:DC:1F:6E:92:0E:AF:25:CB:CD:E5:72
            X509v3 Authority Key Identifier:
                keyid:46:26:E1:CC:8E:40:91:32:31:DC:1F:6E:92:0E:AF:25:CB:CD:E5:72
                DirName:/C=US/ST=CA/L=San Jose/O=Google/OU=Engineering/CN=OT Fake CA certificate
                serial:1A:8F:86:2B:3C:75:83:2B:B2:FF:2B:7B:13:81:7A:70:20:AC:0A:62

            X509v3 Basic Constraints: critical
                CA:TRUE
            X509v3 Key Usage:
                Digital Signature, Certificate Sign, CRL Sign
    Signature Algorithm: ecdsa-with-SHA256
         30:45:02:20:53:b5:ed:9e:20:34:e5:8b:b8:54:75:78:14:64:
         eb:71:4b:a2:67:9c:a7:a7:96:3e:88:13:c8:e7:22:7c:94:0a:
         02:21:00:c1:9f:71:92:27:b2:47:bb:98:58:3f:08:a9:ef:d8:
         db:9e:12:5c:30:a6:2e:72:b1:c8:63:b9:8c:4c:ee:ab:a5
-----BEGIN CERTIFICATE-----
MIIC4jCCAoigAwIBAgIUGo+GKzx1gyuy/yt7E4F6cCCsCmIwCgYIKoZIzj0EAwIw
dTELMAkGA1UEBhMCVVMxCzAJBgNVBAgMAkNBMREwDwYDVQQHDAhTYW4gSm9zZTEP
MA0GA1UECgwGR29vZ2xlMRQwEgYDVQQLDAtFbmdpbmVlcmluZzEfMB0GA1UEAwwW
T1QgRmFrZSBDQSBjZXJ0aWZpY2F0ZTAeFw0yNDA0MDIwMTA2NDJaFw0zNDAzMzEw
MTA2NDJaMHUxCzAJBgNVBAYTAlVTMQswCQYDVQQIDAJDQTERMA8GA1UEBwwIU2Fu
IEpvc2UxDzANBgNVBAoMBkdvb2dsZTEUMBIGA1UECwwLRW5naW5lZXJpbmcxHzAd
BgNVBAMMFk9UIEZha2UgQ0EgY2VydGlmaWNhdGUwWTATBgcqhkjOPQIBBggqhkjO
PQMBBwNCAAQdBVpF5ZI86uUEenT2yIwMInQWFRi13518XvgOQqV34Aw8GrJDeImW
tKp/9mKGft2hu7tiAfLWmVaDvlERYXCRo4H1MIHyMB0GA1UdDgQWBBRGJuHMjkCR
MjHcH26SDq8ly83lcjCBsgYDVR0jBIGqMIGngBRGJuHMjkCRMjHcH26SDq8ly83l
cqF5pHcwdTELMAkGA1UEBhMCVVMxCzAJBgNVBAgMAkNBMREwDwYDVQQHDAhTYW4g
Sm9zZTEPMA0GA1UECgwGR29vZ2xlMRQwEgYDVQQLDAtFbmdpbmVlcmluZzEfMB0G
A1UEAwwWT1QgRmFrZSBDQSBjZXJ0aWZpY2F0ZYIUGo+GKzx1gyuy/yt7E4F6cCCs
CmIwDwYDVR0TAQH/BAUwAwEB/zALBgNVHQ8EBAMCAYYwCgYIKoZIzj0EAwIDSAAw
RQIgU7XtniA05Yu4VHV4FGTrcUuiZ5ynp5Y+iBPI5yJ8lAoCIQDBn3GSJ7JHu5hY
Pwip79jbnhJcMKYucrHIY7mMTO6rpQ==
-----END CERTIFICATE-----
$
```
