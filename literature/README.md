# Local literature archive

This directory contains a version-pinned local PDF for every paper in [`docs/literature.md`](../docs/literature.md) and [`claims/registry.json`](../claims/registry.json). Filenames include the repository paper ID and the source version so a later upstream revision cannot silently replace the evidence used by a run.

[`manifest.json`](manifest.json) records the canonical source, exact retrieval URL, byte count, page count, and SHA-256 digest for each file. Verify the archived bytes from this directory with:

```sh
shasum -a 256 -c SHA256SUMS
```

`CZ24` is the original nine-page AMS publisher PDF. The AMS endpoint is browser-protected, so its raw publisher file was retrieved from the Internet Archive's 2023-12-14 capture; both URLs are recorded in the manifest.

The PDFs retain their respective authors' and publishers' copyright and licensing terms. They are source material for the repository and are not relicensed by the surrounding project.
