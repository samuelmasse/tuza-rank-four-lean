"""Create the deterministic TeX source archive submitted to arXiv."""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Final, cast
from zipfile import ZIP_STORED, ZipFile, ZipInfo


ARCHIVE_FILES: Final[tuple[tuple[str, str], ...]] = (
    ("paper/main.tex", "main.tex"),
    ("paper/tuza-rank-four.bib", "tuza-rank-four.bib"),
)
ZIP_TIMESTAMP: Final[tuple[int, int, int, int, int, int]] = (1980, 1, 1, 0, 0, 0)


@dataclass(frozen=True)
class Arguments:
    repository: Path
    output: Path


def parse_args() -> Arguments:
    repository_default = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repository",
        type=Path,
        default=repository_default,
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=repository_default / "output" / "arxiv" / "tuza-rank-four-arxiv.zip",
    )
    namespace = parser.parse_args()
    return Arguments(
        repository=cast(Path, namespace.repository).resolve(),
        output=cast(Path, namespace.output).resolve(),
    )


def archive_info(name: str) -> ZipInfo:
    info = ZipInfo(filename=name, date_time=ZIP_TIMESTAMP)
    info.compress_type = ZIP_STORED
    info.create_system = 3
    info.external_attr = 0o100644 << 16
    return info


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def build_archive(repository: Path, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with ZipFile(output, mode="w") as archive:
        for source_name, archive_name in ARCHIVE_FILES:
            source = repository / source_name
            archive.writestr(archive_info(archive_name), source.read_bytes())
    print(f"wrote {output}")
    print(f"sha256:{sha256(output)}")


def main() -> None:
    arguments = parse_args()
    build_archive(arguments.repository, arguments.output)


if __name__ == "__main__":
    main()
