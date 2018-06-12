var nanoiterator = require('nanoiterator')
var inherits = require('inherits')
var hash = require('./hash')
var options = require('./options')

var SORT_GT = [3, 2, 1, 0]
var SORT_GTE = [3, 2, 1, 0, 4]

module.exports = Iterator

function Iterator (db, prefix, opts) {
  if (!(this instanceof Iterator)) return new Iterator(db, prefix, opts)
  if (!opts) opts = {}

  nanoiterator.call(this)

  this._db = db
  this._latestNodes = []
  this._prefixStack = []
  this._pendingStack = []
  this._stack = [{
    path: prefix ? hash(prefix, false) : [],
    node: null,
    i: 0
  }]

  this._recursive = opts.recursive !== false
  this._gt = !!opts.gt
  this._start = this._stack[0].path.length
  this._end = this._recursive ? Infinity : this._start + hash.LENGTH
  this._map = options.map(opts, db)
  this._reduce = options.reduce(opts, db)
  this._collisions = []

  this._prefix = prefix
  this._pending = 0
  this._error = null
}

inherits(Iterator, nanoiterator)

Iterator.prototype._pushPointer = function (ptr, i, cb) {
  var self = this
  var top = {path: null, node: null, i}

  this._pending++
  this._pendingStack.push(top)
  this._db._getPointer(ptr.feed, ptr.seq, false, done)

  function done (err, node) {
    if (err) self._error = err
    else top.node = node
    if (--self._pending) return
    if (self._error) return cb(self._error)
    self._next(cb)
  }
}

Iterator.prototype._pushNode = function (node, i) {
  this._pendingStack.push({
    path: null,
    node,
    i
  })
}

Iterator.prototype._pushPrefix = function (path, i, val) {
  console.log('PUSHED PREFIX')
  this._prefixStack.push({
    path: (i < path.length ? path.slice(0, i) : path).concat(val),
    node: null,
    i
  })
}

Iterator.prototype._allNodes = function (top, cb) {
  var node = top.node
  var end = Math.min(this._end, node.trie.length)
  // start from the last path index
  for (var i = top.i; i < end; i++) {
    // check if there is a trie at this path index which leads to keys
    var bucket = i < node.trie.length && node.trie[i]
    // if not keep looking
    if (!bucket) continue
    // get the hash value at i
    var val = node.path[i]
    var order = this._sortOrder(i)

    // look at index in the bucket to follow the trie
    for (var j = 0; j < order.length; j++) {
      // what order do we want to go through the bucket
      // this is reverse hash order so that the stack is pushed in the hash order
      // TODO: what order for latest?
      var sortValue = order[j]
      // the bucket can be smaller sort array
      var values = sortValue < bucket.length && bucket[sortValue]
      // if this sort index is the same as the current path index
      if (sortValue === val) {
        // and there are values in the trie
        // we push the prefix, as this means there are multiple nodes at this path
        if (values) {
          throw new Error('handle multiple values')
          // this._pushPrefix(node.path, i, sortValue)
        }
        // otherwise we push this node back into the stack, with the index incremented.
        // this remains hash sorted because this is pushed in after those with hash order greater,
        // but before those of hash order less than.
        // else this._pushNode(node, i + 1)
        continue
      }
      // if there are no values at this trie continue looking
      if (!values) continue
      // if their are many values this means that there are multiple nodes at this point
      if (values.length > 1) throw new Error('handle multiple values')
      // if (values.length > 1) this._pushPrefix(node.path, i, sortValue)
      // otherwise push a pointer to the next node in this path and keep searching.
      else this._pushPointer(values[0], i + 1, cb)
    }
  }
  if (this._pending === 0) {
    cb(null, this._prereturn([node]))
  } else {
    // note sure if this is the lastest node or not, perhaps it points to a later node.
    this._latestNodes.push([node])
  }
}

// slow case
Iterator.prototype._multiNode = function (path, nodes, cb) {
  if (!nodes.length) return this._next(cb)
  if (nodes.length === 1) {
    this._pushNode(nodes[0], path.length)
    return this._next(cb)
  }
  var ptr = path.length

  if (ptr < this._end) {
    var order = this._sortOrder(ptr)

    for (var i = 0; i < order.length; i++) {
      var sortValue = order[i]
      if (!visitTrie(nodes, ptr, sortValue)) continue
      this._pushPrefix(path, path.length, sortValue)
    }
  }

  nodes = this._filterResult(nodes, ptr)
  this._collisions.push(nodes)
  this._collisions.sort(sortByClockAndSeq)
  this._next(cb)
}

Iterator.prototype._filterResult = function (nodes, i) {
  var result = null
  // sort by key in order to group
  nodes.sort(byKey)

  for (var j = 0; j < nodes.length; j++) {
    var node = nodes[j]
    if (node.path.length !== i && i !== this._end) continue
    if (!isPrefix(node.key, this._prefix)) continue

    if (!result) result = []

    if (result.length && result[0].key !== node.key) {
      // if not deletes
      if (!allDeletes(result)) {
        this._collisions.push(result)
      }
      result = []
    }

    result.push(node)
  }
  return result
}

Iterator.prototype._next = function (cb) {
  // collisions only are generated where there are many nodes
  var nodes = drain(this._collisions)
  // if their are colliding nodes return them
  if (nodes) return cb(null, this._prereturn(nodes))
  if (this._latestNodes.length) {
    // console.log('LATEST _ POP')
    // console.log(this._latestNodes, '\n----\n', this._pendingStack)
    cb(null, this._prereturn(this._latestNodes.pop()))
    return
  }

  var top = null

  while (true) {
    // append pending stack to stack
    if (this._pendingStack.length > 0) {
      // console.log('sort pending stack, and take top')
      this._pendingStack.sort(sortStackByClockAndSeq)
      top = this._pendingStack.pop()
      // console.log(top)
      // console.log(this._pendingStack)
      Array.prototype.push.apply(this._stack, this._pendingStack)
      this._pendingStack = []
    } else {
      top = this._stack.pop()
    }
    // if its the end of the stack we are done
    if (!top) return cb(null, null)
    // if there is node at this point - it means we are at a prefix.
    // stop popping stack and loop up the prefix;
    if (!top.node) return this._lookupPrefix(top.path, cb)
    // if this returns false it means a value has been found so can return from function.
    return this._allNodes(top, cb)
  }
}

Iterator.prototype._lookupPrefix = function (path, cb) {
  var self = this

  this._db.get('', {path, prefix: true, map: false, reduce: false}, done)

  function done (err, nodes) {
    if (err) return cb(err)
    self._multiNode(path, nodes, cb)
  }
}

Iterator.prototype._prereturn = function (nodes) {
  if (this._map) nodes = nodes.map(this._map)
  if (this._reduce) return nodes.reduce(this._reduce)
  return nodes
}

Iterator.prototype._sortOrder = function (i) {
  var gt = this._gt || !this._start
  return gt && this._start === i ? SORT_GT : SORT_GTE
}

function byKey (a, b) {
  var k = b.key.localeCompare(a.key)
  return k || b.feed - a.feed
}

function allDeletes (nodes) {
  for (var i = 0; i < nodes.length; i++) {
    if (nodes[i].value) return false
  }
  return true
}

function visitTrie (nodes, ptr, val) {
  for (var i = 0; i < nodes.length; i++) {
    var node = nodes[i]
    var bucket = ptr < node.trie.length && node.trie[ptr]
    if (bucket && bucket[val]) return true
    if (node.path[ptr] === val) return true
  }
  return false
}

function drain (collisions) {
  while (collisions.length) {
    var collision = collisions.pop()
    if (allDeletes(collision)) continue
    return collision
  }

  return null
}

function isPrefix (s, prefix) {
  if (!prefix) return true
  if (s.startsWith) return s.startsWith(prefix)
  return s.slice(0, prefix.length) === prefix
}

function sortNodesByClock (a, b) {
  var isGreater = false
  var isLess = false
  var length = a.clock.length
  if (b.clock.length > length) length = b.clock.length
  for (var i = 0; i < length; i++) {
    var diff = (a.clock[i] || 0) - (b.clock[i] || 0)
    if (diff > 0) isGreater = true
    if (diff < 0) isLess = true
  }
  if (isGreater && isLess) return 0
  if (isLess) return -1
  if (isGreater) return 1
  return 0
}

function sortStackByClockAndSeq (a, b) {
  return sortByClockAndSeq(a.node, b.node)
}

function sortByClockAndSeq (a, b) {
  if (a && !b) return -1
  if (b && !a) return 1
  if (!a && !b) return 0
  var sortValue = sortNodesByClock(a, b)
  if (sortValue !== 0) return sortValue
  // // same time, so use sequence to order
  if (a.feed === b.feed) return a.seq - b.seq
  var bOffset = b.clock.reduce((p, v) => p + v, b.seq)
  var aOffset = a.clock.reduce((p, v) => p + v, a.seq)
  // if real sequence is the same then return sort on feed
  if (bOffset === aOffset) return b.feed - a.feed
  return aOffset - bOffset
}
