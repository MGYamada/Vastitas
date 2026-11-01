#!/usr/bin/env python3
"""Export a verified compact record, without caches or large Lean executables."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

from verify import backend, verify


def export(source,destination):
    source,destination = Path(source).resolve(),Path(destination).resolve()
    if destination.is_relative_to(source): raise ValueError('archive must be outside its input record')
    summary = verify(source)
    reader = backend.Reader(source)
    record = reader.json('record.json')
    names = sorted(set(record['files'])|{'record.json'})
    destination.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(destination,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as out:
        for name in names:
            info = zipfile.ZipInfo(name,date_time=(2026,11,1,0,0,0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            out.writestr(info,reader.read(name),compresslevel=9)
    if verify(destination)!=summary: raise ValueError('archive replay differs')
    data = destination.read_bytes()
    manifest = {'schema':1,'archive':destination.name,'sha256':hashlib.sha256(data).hexdigest(),
        'bytes':len(data),'members':len(names),'measured_head':record['head'],'measured_status':record['status'],
        'backend_head':reader.json(record['backend_record']+'/record.json')['repository']['head'],
        'excluded_executable_fingerprints':record['binaries'],'summary':summary}
    destination.with_name('artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('record',type=Path)
    parser.add_argument('archive',type=Path)
    args=parser.parse_args()
    result=export(args.record,args.archive)
    print(json.dumps({k:v for k,v in result.items() if k not in ('excluded_executable_fingerprints','summary')},indent=2))
