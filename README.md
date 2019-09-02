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

3. Install [BUM](https://github.com/o89/bum).

4. And:

    ```shell
    $ git clone https://github.com/o89/n2o/
    $ cd n2o
    $ bum compile
    ```
