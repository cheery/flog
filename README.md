# FLOG programming language in RPython runtime

### How to build

 1. Ensure you have Python installed.
 2. Download the pypy runtime and extract it.
 3. Locate the rpython and run it on the `runtime/goal_standalone.py`.

Sequence of terminal commands that do the trick:

```
wget https://downloads.python.org/pypy/pypy3.8-v7.3.7-src.tar.bz2
tar -xf pypy3.8-v7.3.7-src.tar.bz2
pypy3.8-v7.3.7-src/rpython/bin/rpython runtime/goal_standalone.py 
```

On successful compile you obtain the `flog` -executable.
