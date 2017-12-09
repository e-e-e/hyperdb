# HyperDB Architecture

HyperDB is a scalable peer-to-peer key-value database.

## Filesystem metaphor

HyperDB is structured to be used much like a traditional hierarchical
filesystem. A value can be written and read at locations like `/foo/bar/baz`,
and the API supports querying or tracking values at subpaths, like how watching
for changes on `/foo/bar` will report both changes to `/foo/bar/baz` and also
`/foo/bar/19`.

## Set of append-only logs

A HyperDB is fundamentally a set of
[hypercore](https://github.com/mafintosh/hypercore)s. A *hypercore* is a secure
append-only log that is identified by a public key, and can only be written to
by the holder of the corresponding private key. Because it is append-only, old
values cannot be deleted nor modified. Because it is secure, any other peer in
the network can verify these attributes without inherently trusting the author.

Each entry in a hypercore has a *sequence number*, that increments by 1 with
each write, starting at 0 (`seq=0`).

HyperDB builds its hierarchical key-value store on top of these hypercores, and
also provides facilities for authorization, and replication of those member
hypercores.

### Directed acyclic graph

The combination of all operations performed on a HyperDB by all of its members
forms a DAG (*directed acyclic graph*). Each database operations link backward
to all of the known "heads" in the graph.

For example, let's say Alice starts a new HyperDB and writes 2 values to it:

```
// Feed

0 (/foo/bar = 'baz')
1 (/foo/2   = '{ "some": "json" }')


// Graph

Alice:  0  <---  1
```

Where sequence number 1 (the second entry) refers to sequence number 0 on the
same feed (Alice's).

Now Alice *authorizes* Bob to write to the HyperDB. Internally, this means Alice
writes a special message to her feed saying that Bob's feed (identified by his
public key) should be read and replicated in by other participants. Her feed
becomes

```
// Feed

0 (/foo/bar = 'baz')
1 (/foo/2   = '{ "some": "json" }')
2 (''       = '')


// Graph

Alice: 0  <---  1  <---  2
```

Authorization is formatted internally in a special way so that it isn't
interpreted as a key/value pair.

Now Bob writes a value to his feed, and then Alice and Bob sync. The result is:

```
// Feed

//// Alice
0 (/foo/bar = 'baz')
1 (/foo/2   = '{ "some": "json" }')
2 (''       = '')

//// Bob
0 (/a/b     = '12')


// Graph

Alice: 0  <---  1  <---  2
Bob  : 0
```

Notice that none of Alice's entries refer to Bob's, and vice versa. This is
because neither has written any entries to their feeds since the two became
aware of each other (authorized & replicated each other's feeds).

Next, Alice writes a new value, and her latest entry will refer to Bob's:

```
// Feed

//// Alice
0 (/foo/bar = 'baz')
1 (/foo/2   = '{ "some": "json" }')
2 (''       = '')
3 (/foo/hup = 'beep')

//// Bob
0 (/a/b     = '12')


// Graph

Alice: 0  <---  1  <---  2  <--/  3
Bob  : 0  <-------------------/
```

Because Alice's latest feed entry refers to Bob's latest feed entry, there is
now only one "head" in the database. That means there is enough information in
Alice's seq=3 entry to find any other key in the database. In the last example,
there were two heads (Alice's seq=2 and Bob's seq=0); both of which would need
to be read internally in order to locate any key in the database.

## Authorization

The set of hypercores are *authorized* in that the original author of the first
hypercore in a hyperdb must explicitly denote in their append-only log that the
public key of a new hypercore is permitted to edit the database. Any authorized
member may authorize more members. There is no revocation or other author
management elements currently.

## Incremental index

HyperDB builds an *incremental index* with every new key/value pairs ("nodes")
written. This means a separate data structure doesn't need to be maintained
elsewhere for fast writes and lookups: each node written has enough information
to look up any other key quickly and otherwise navigate the database.

Each node stores the following basic information:

- `key`: the key that is being created or modified. e.g. `/home/sww/dev.md`
- `value`: the value stored at that key.
- `seq`: the sequence number of this entry in the owner's hypercore. 0 is the
  first, 1 the second, and so forth.
- `feed`: the ID of the hypercore writer that wrote this
- `prefix`: a 2-bit hash sequence of the key's components
- `trie`: a navigation structure used with `prefix` to find a desired key
- `clock`: vector clock to determine node insertion causality
- `feeds`: an array of { feedKey, seq } for decoding a `clock`

### Vector clock

Each node stores a [vector clock](https://en.wikipedia.org/wiki/Vector_clock) of
the last known sequence number from each feed it knows about. This is what forms
the DAG structure.

For example, Alice's vector clock on her seq=3 entry above would be `[3, 0]`
since she knows of her latest entry (seq=3) and Bob's (seq=0).

*TODO: is this correct? ^^^*

### Prefix trie

...

