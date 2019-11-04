# Installation instructions

This has been tested with python 3.7.4 and 3.7.5.

## Setup virtualenv

```
pip3 install virtualenv
virtualenv venv
source venv/bin/activate
```

## Build z3

Building z3 might take a while.

```
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

## Docker

You can build a development environment with

```
make build-dev
```

And start a development environment with

```
make create-dev
```

# Running the Synthesizer

You can check out the usage help with

```
python src/runsynth.py --help
```

For example, you can run the demo with

```
python src/runsynth.py -e 2 demo.json
```

## Input

The synthesizer takes input/output examples in json format. Check out
[demo.json](./demo.json) for an example file.

You can specify an input/output example in the following way:

```javascript
{
    "inputs": [
        {
            "Left": "John Michael Doe"
        },
        {
            "Right": 4
        }
    ],
    "output": {
        "Left": "John"
    }
}
```

`"Left"` means we have an element of `Text`, while `"Right"` means we
have an `Integer`.

# Help

Please submit an issue if there's anything unclear.
