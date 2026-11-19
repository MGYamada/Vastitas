"""Offline record epoch checks; these never grant compiler acceptance.

Current records declare the compiler's sole wire epoch. Metadata-absent epoch-8
records are replayable only for the retained metadata identities below, after
all existing semantic/file checks. They are never re-emitted through the kernel.
"""
import hashlib
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
_spec = importlib.util.spec_from_file_location('record_kernel_protocol', ROOT / 'scripts/kernel_protocol.py')
_protocol = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_protocol)
CURRENT_PROTOCOL = _protocol.CURRENT_PROTOCOL

# SHA-256 of the exact retained environment.json / record.json bytes. These pins
# identify the historical record schema, not a theorem or source/native proof.
HISTORICAL_METADATA = {
    'allocation-audit': {
        '70c828fe6cb84df87ee751b793a269a98f6e9ed5670240868c8b571fc5ed8cee',  # macos-production
    },
    'source-workspace': {
        'f76ddea9848d9d16e26a45139dc5d8c64b4448002f5a985e15893e3daaa916e7',  # linux
        'e0f05732d0d6d51e8ebbe10b3b4143523c7c9b7e5a3a31fcbd8b8d92d3d044bc',  # linux-allocator
        '0b5d29c8e4f292166a6ede5affdbffde177a9d0de0224db7681651026c3c3f7a',  # linux-packing
        'd52a8237e8b98433fdfd04147d3ec2c1046ca5420fa38865f37375dafa619b97',  # linux-streaming
        '4da7980ddae5bc03f053f0cdf628932700e820a706806e95211a7e27623cdb23',  # linux-unit-cleanup
        'f1d2ee7a6ff7e4c400ada917ee175632710984956b74a8f6f2e56d503dfe7558',  # macos
        'cb1f960094793bb59cb085fab3017afe0c6fcd7af0d2aa4050a2cb0dbdb2cfb9',  # macos-allocator
        '9a9e6926daeed165b5288bf53c77a82398c5edba399be82e86da5921dd48f758',  # macos-packing
        'a4f74966cf91bab8a369f187244400aac41f6b186bdd177a14669c8a39302f83',  # macos-streaming
        '86394e1c6d45d1d1cea8caec07bcf76d4d01581a29a922b4640596b1fae0a4a4',  # macos-unit-cleanup
        '0b65f30caa5533c948045149dcf5e0f459d68d4712a7ccf29d1dd6980ea4b3b4',  # linux-lifetimes
        '2088c328b0b8d2cd48088b4ee7eef3df90d3861da115d29af5a3039f97b93aec',  # macos-lifetimes
        '1a6cb082094c86c625c87c90af44c849a289beda056f093e5355e42c845a5163',  # macos-lifetimes-streaming
    },
}


def declared(metadata):
    """Select the current epoch, or the restricted historical replay branch."""
    if 'wire_epoch' not in metadata:
        return 8
    epoch = metadata['wire_epoch']
    if type(epoch) is not int or epoch != CURRENT_PROTOCOL:
        raise ValueError('record wire_epoch must be the current compiler epoch')
    return epoch


def envelopes(epoch, *documents):
    """Every normal/failure input and response belongs to this one epoch."""
    if type(epoch) is not int or epoch not in (8, CURRENT_PROTOCOL):
        raise ValueError('unsupported record wire epoch')
    for document in documents:
        if (not isinstance(document, dict) or type(document.get('version')) is not int or
                document['version'] != epoch):
            raise ValueError('record wire/response epoch mismatch')


def input_binding(command, data):
    if command.get('stdin') != {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}:
        raise ValueError('record actual kernel input does not match retained wire bytes')


def historical_identity(metadata, raw_metadata, family):
    """Call after semantic replay so retained mutation tests remain specific."""
    declared(metadata)
    if 'wire_epoch' not in metadata and hashlib.sha256(raw_metadata).hexdigest() not in HISTORICAL_METADATA[family]:
        raise ValueError('unknown metadata-absent historical record; current records require wire_epoch')
