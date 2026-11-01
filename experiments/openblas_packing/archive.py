#!/usr/bin/env python3
"""Export the entire verified packing record with deterministic ZIP metadata."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile
from verify import verify, workspace


def export(source,destination):
    source,destination=Path(source).resolve(),Path(destination).resolve()
    if destination.is_relative_to(source): raise ValueError('archive must be outside record')
    summary=verify(source); reader=workspace.Reader(source)
    destination.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(destination,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as out:
        for name in sorted(reader.names):
            entry=zipfile.ZipInfo(name,date_time=(2026,11,1,0,0,0)); entry.compress_type=zipfile.ZIP_DEFLATED
            entry.external_attr=0o100644<<16; out.writestr(entry,reader.read(name),compresslevel=9)
    if verify(destination)!=summary: raise ValueError('archive replay differs')
    record=reader.json('record.json'); data=destination.read_bytes()
    manifest={'schema':1,'archive':destination.name,'sha256':hashlib.sha256(data).hexdigest(),
              'bytes':len(data),'members':len(reader.names),'repository':record['repository'],
              'summary':summary}
    destination.with_name('artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('record',type=Path); parser.add_argument('archive',type=Path)
    args=parser.parse_args(); result=export(args.record,args.archive)
    print(json.dumps({k:v for k,v in result.items() if k not in ('repository','summary')},indent=2))
