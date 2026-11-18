"""Package the files listed in SHA256SUMS as a reproducible standalone tar."""
from hashlib import file_digest
from pathlib import Path
import tarfile
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent
PACKAGE = "permutation-supersequence-10"


def main():
    manifest = ROOT / "SHA256SUMS"
    files = {manifest.name: None}
    for line in manifest.read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or name in files:
            raise ValueError(f"invalid manifest path {name}")
        files[name] = digest

    output = ROOT / "dist" / f"{PACKAGE}.tar"
    output.parent.mkdir(exist_ok=True)
    with TemporaryDirectory(dir=output.parent) as work:
        temporary = Path(work) / output.name
        with tarfile.open(temporary, "w", format=tarfile.USTAR_FORMAT) as archive:
            for name, digest in sorted(files.items()):
                with (ROOT / name).open("rb") as source:
                    if digest and file_digest(source, "sha256").hexdigest() != digest:
                        raise ValueError(f"checksum mismatch for {name}")
                    entry = tarfile.TarInfo(f"{PACKAGE}/{name}")
                    entry.size = source.seek(0, 2)
                    source.seek(0)
                    archive.addfile(entry, source)
        temporary.replace(output)


if __name__ == "__main__":
    main()
