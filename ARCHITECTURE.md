# HyperDB architecture

HyperDB is a scalable peer-to-peer key-value database.

intro /w file system metaphor

## Set of append-only logs

A HyperDB is fundamentally a set of authorized
[hypercore](https://github.com/mafintosh/hypercore)s. A *hypercore* is a secure
append-only log that is identified by a public key, and can only be written to
by the holder of the corresponding private key. Because it is append-only, old
values cannot be deleted nor modified. Because it is secure, any other peer in
the network can verify these attributes without inherently trusting the author.

HyperDB builds a hierarchical key-value store on top of these hypercores, and
also provides facilities for authorization, and replication of the member
hypercores.

## Hierarchical

The key-value store is hierarchical in that the key space models a tree, like a
file system. Storing `foo=bar` is equivalent to `/foo=bar`, which differs from
`/foo/baz=bar`, where `baz` is a subdirectory of `foo`. Many features of HyperDB
exploit the ability to reference a subset of keys by a common prefix, e.g.
`/foo`.

## Incremental index

HyperDB builds an *incremental index* as new key/value pairs ("nodes") are
written to it. This means a separate index data structure doesn't need to be
maintained anywhere else: each node written has enough information to look up
any other key quickly and otherwise navigation the data structure.

Each node stores the following information:

- `key`: the key that is being created or modified. e.g. `/home/sww/dev.md`
- `value`: the value stored at that key.
- `seq`: the sequence number of this entry in the owner's hypercore. 0 is the
  first, 1 the second, and so forth.
- `feed`: the ID of the hypercore writer that wrote this
- `prefix`: a 2-bit hash sequence of the key's components
- `trie`: a navigation structure used with `prefix` to find a desired key
- `clock`: vector clock to determine node insertion causality
- `feeds`: an array of { feedKey, seq } for decoding a `clock`

### Directed acyclic graph

The combination of these properties form a *directed acyclic graph* (DAG).

## Authorization

The set of hypercores are *authorized* in that the original author of the first
hypercore in a hyperdb must explicitly denote in their append-only log that the
public key of a new hypercore is permitted to edit the database. Any authorized
member may authorize more members. There is no revocation or other author
management elements currently.

