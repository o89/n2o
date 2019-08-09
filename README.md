# N2O for Lean 4

## Build

UNIX-like OS:

1. First, build Lean 4:

    ```shell
    $ git clone https://github.com/leanprover/lean4
    $ mkdir lean4/build
    $ cd lean4/build
    $ cmake ../src
    $ make
    ```

2. Then build libwebsockets:

    ```shell
    $ git clone https://github.com/warmcat/libwebsockets
    $ mkdir libwebsockets/build
    $ cd libwebsockets/build
    $ cmake ..
    $ make
    $ sudo make install
    ```

3. And:

    ```shell
    $ git clone https://github.com/o89/n2o/
    $ cd n2o
    $ LEAN_DIR=/path/to/lean4 make
    ```

## Run

```shell
$ wscat -c ws://127.0.0.1/ws/ -s n2o
connected (press CTRL+C to quit)
> helo
< helo
>
```
