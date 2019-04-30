# Installation instructions

## Setup virtualenv

```
pip3 install virtualenv
virtualenv venv
source venv/bin/activate
```

## Get z3

```
git clone https://github.com/Z3Prover/z3.git

cd z3
python scripts/mk_make.py --python

cd build
make
make install
```

## Testing

```
pip3 install pytest
```
