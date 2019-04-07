import argparse
import base64
import os
import zlib
from pathlib import Path


def convert(s):
    b = base64.b64decode(s.encode('ascii'))
    return zlib.decompress(b).decode('utf-8')


ACTIVATE_THIS = convert("""
eJyNU01v2zAMvetXEB4K21jnDOstQA4dMGCHbeihlyEIDMWmE62yJEiKE//7kXKdpEWLzYBt8evx
kRSzLPs6wiEoswM8YdMpjUXcq1Dz6RZa1cSiTkJdr86GsoTRHuCotBayiWqQEYGtMCgfD1KjGYBe
5a3p0cRKiEe2NtLAFikftnDco0ko/SFEVgEZ8aRCZDIPY9xbA8pE9M4jfW/B2CjiHq9zbJVZuOQq
siwTIvpxKYCembPAU4Muwi/Z4zfvrZ/MXipKeB8C+qisSZYiWfjJfs+0/MFMdWn1hJcO5U7G/SLa
xVx8zU6VG/PXLXvfsyyzUqjeWR8hjGE+2iCE1W1tQ82hsCJN9dzKaoexyB/uH79TnjwvxcW0ntSb
yZ8jq1Z5Q1UXsyy3gf9nbjTEj7NzQMfCJa/YSmrQ+2D/BqfiOi6sclrGzvoeVivIj8rcfcmnIQRF
7XCyeZI7DFe5/lhlCs5PRf5QW66VXT/NrlQ46oD/D6InkOmi3IQcbhKxAX2g4a+Xd5s3UtCtG2py
m8eg6WYWqR6SL5OjKMGfSrYt/6kxxQtOpeAgj1LXBNmpE2ElmCSIy5H0zFd8gJ924HWijWhb2hRC
6wNEm1QdDZtuSZcEprIUBo/XRNcbQe1OUbQ/r3hPTaPJJDNtFLu8KHV5XoNr3Eo6h6YtOKw8e8yw
VF5PnJ+ts3a9/Mz38RpG/AUSzYUW
""")


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--virtualenv-dir', default=os.environ['VIRTUAL_ENV'])

    args = parser.parse_args()

    activate_this_path = Path(args.virtualenv_dir) / 'bin/activate_this.py'

    print(f'Writing activate_this.py to {activate_this_path}')
    with open(activate_this_path, 'w') as fp:
        fp.write(ACTIVATE_THIS)
