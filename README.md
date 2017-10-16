BoolServ
========

技術書典3で頒布する進捗大陸02で作る分散システムのソースコード。
`true` または `false` のどちらかを保存する状態機械を Raft で複製させたシステムです。

Prerequisite
------------

- Coq 8.6 (installed by opam)
- opam

Compilation
-----------

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install verdi verdi-raft verdi-runtime
make
```

Run
---

```
./boolserv.native -debug -node 0,localhost:9000 \
                         -node 1,localhost:9001 \
                         -node 2,localhost:9002 \
                         -me 0 -port 8000
```

```
./boolserv.native -debug -node 0,localhost:9000 \
                         -node 1,localhost:9001 \
                         -node 2,localhost:9002 \
                         -me 1 -port 8001
```

```
./boolserv.native -debug -node 0,localhost:9000 \
                         -node 1,localhost:9001 \
                         -node 2,localhost:9002 \
                         -me 2 -port 8002
```

Control
------

```
$ python client/boolserv_ctl.py \
    --cluster "localhost:8000,localhost:8001,localhost:8002" status
localhost:8000 is leader
localhost:8001 is not leader
localhost:8002 is not leader
$ python client/boolserv_ctl.py \
    --cluster "localhost:8000,localhost:8001,localhost:8002" get
false
$ python client/boolserv_ctl.py \
    --cluster "localhost:8000,localhost:8001,localhost:8002" put true
true
$ python client/boolserv_ctl.py \
    --cluster "localhost:8000,localhost:8001,localhost:8002" get
true
```
