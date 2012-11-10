dagre.layout.order = function() {
  var config = {
    iterations: 24, // max number of iterations
    debugLevel: 0
  };

  var timer = createTimer();

  var self = {};

  self.iterations = propertyAccessor(self, config, "iterations");

  self.debugLevel = propertyAccessor(self, config, "debugLevel", function(x) {
    timer.enabled(x);
  });

  self.run = timer.wrap("Order Phase", run);

  return self;

  /*
   * `g` is the graph to order, `cg` is the constraint graph, where the edge
   * `(u, v)` in `cg` indicates that `u` must be to the left of `v`.
   */
  function run(g, cg) {
    var layering = initOrder(g);
    var bestLayering = layering;
    var bestCC = Number.POSITIVE_INFINITY;

    if (config.debugLevel >= 2) {
      console.log("Order phase start cross count: " + bestCC);
    }

    var cc, i, lastBest;
    for (i = 0, lastBest = 0; lastBest < 4 && i < config.iterations; ++i, ++lastBest) {
      cc = sweep(g, cg, i, layering);
      if (cc < bestCC) {
        bestLayering = copyLayering(layering);
        bestCC = cc;
        lastBest = 0;
      }
      if (config.debugLevel >= 3) {
        console.log("Order phase iter " + i + " cross count: " + bestCC);
      }
    }

    bestLayering.forEach(function(layer) {
      layer.forEach(function(u, i) {
        g.node(u).order = i;
      });
    });

    if (config.debugLevel >= 2) {
      console.log("Order iterations: " + i);
      console.log("Order phase best cross count: " + bestCC);
    }

    return bestLayering;
  }

  function initOrder(g) {
    var layering = [];
    g.eachNode(function(n, a) {
      var layer = layering[a.rank] || (layering[a.rank] = []);
      layer.push(n);
    });
    return layering;
  }

  function sweep(g, cg, iter, layering) {
    var cc = 0,
        i;
    if (iter % 2 === 0) {
      for (i = 1; i < layering.length; ++i) {
        layering[i] = barycenterLayer(g, cg, layering[i - 1], layering[i], "inEdges");
        cc += bilayerCrossCount(g, layering[i-1], layering[i]);
      }
    } else {
      for (i = layering.length - 2; i >= 0; --i) {
        layering[i] = barycenterLayer(g, cg, layering[i + 1], layering[i], "outEdges");
        cc += bilayerCrossCount(g, layering[i], layering[i+1]);
      }
    }
    return cc;
  }

  /*
   * Given a fixed layer and a movable layer in a graph this function will
   * attempt to find an improved ordering for the movable layer such that
   * edge crossings may be reduced.
   *
   * This algorithm is based on the barycenter heuristic and the constrained
   * crossing reduction function described in Forster, "A Fast and Simple
   * Heuristic for Constrainted Tow-Level Crossing Reduction".
   */
  function barycenterLayer(g, cg, fixed, movable, neighbors) {
    var pos = layerPos(movable),
        bs = barycenters(g, fixed, movable, neighbors),
        ls = {},
        counter = 0;

    // Select only constraints relevant to this layer
    cg = cg.subgraph(movable.filter(function(u) { return cg.hasNode(u); }));

    // Create singleton lists for each node
    movable.forEach(function(u) {
      ls[u] = {
        weight: bs[u],
        pos: pos[u],
        nodes: [u]
      };
    });

    var e;
    while ((e = findViolatedConstraint(cg, ls)) != null) {
      var s = cg.source(e),
          degS = g[neighbors](s).length,
          t = cg.target(e),
          degT = g[neighbors](s).length,
          u = "_A" + ++counter,
          b = (ls[s].weight * degS + ls[t].weight * degT) / (degS + degT);
          pos = Math.min(ls[s].pos, ls[t].pos);

      ls[u] = { weight: b, pos: pos, nodes: ls[s].nodes.concat(ls[t].nodes) };
      delete ls[s];
      delete ls[t];

      cg.addNode(u);
      replaceNode(u, s);
      replaceNode(u, t);
      cg.delNode(s);
      cg.delNode(t);
    }

    var sorted = values(ls).sort(function(x, y) {
      return x.weight - y.weight || x.pos - y.pos;
    });

    var result = [];
    sorted.forEach(function(x) {
      result = result.concat(x.nodes);
    });
    return result;

    function replaceNode(o, n) {
      cg.inEdges(o).forEach(function(e) {
        if (!cg.source(e) === n)
          cg.addEdge("_S" + ++counter, cg.source(e), n);
        cg.delEdge(e);
      });
      cg.outEdges(o).forEach(function(e) {
        if (!cg.target(e) === n)
          cg.addEdge("_S" + ++counter, n, cg.target(e));
        cg.delEdge(e);
      });
    }
  }

  function findViolatedConstraint(cg, ls) {
    var active = [],
        incoming = {},
        incomingCount = {};

    cg.eachNode(function(u) {
      incoming[u] = [];
      incomingCount[u] = cg.inEdges(u).length;
      if (cg.predecessors(u).length === 0) {
        active.push(u);
      }
    });

    while (active.length) {
      var u = active.pop();
      for (var k in incoming[u]) {
        var e = incoming[u][k],
            s = cg.source(e);
        if (ls[s].weight >= ls[u].weight)
          return e;
      }
      cg.outEdges(u).forEach(function(e) {
        var t = cg.target(e),
            inc = incoming[t];
        inc.unshift(e);
        if (--incomingCount[t] === 0) {
          active.push(t);
        }
      });
    }

    return null;
  }

  /*
   * Given a fixed layer and a movable layer in a graph, this function will
   * return weights for the movable layer that can be used to reorder the layer
   * for potentially reduced edge crossings.
   */
  function barycenters(g, fixed, movable, neighbors) {
    var fixedPos = layerPos(fixed);

    var bs = {};
    movable.forEach(function(u) {
      var b = -1;
      var edges = g[neighbors](u);
      if (edges.length > 0) {
        b = 0;
        edges.forEach(function(e) {
          var source = g.source(e);
          var neighborId = source === u ? g.target(e) : source;
          b += fixedPos[neighborId];
        });
        b = b / edges.length;
      }
      bs[u] = b;
    });

    return bs;
  }

  function copyLayering(layering) {
    return layering.map(function(l) { return l.slice(0); });
  }
}

var crossCount = dagre.layout.order.crossCount = function(g, layering) {
  var cc = 0;
  var prevLayer;
  layering.forEach(function(layer) {
    if (prevLayer) {
      cc += bilayerCrossCount(g, prevLayer, layer);
    }
    prevLayer = layer;
  });
  return cc;
}

/*
 * This function searches through a ranked and ordered graph and counts the
 * number of edges that cross. This algorithm is derived from:
 *
 *    W. Barth et al., Bilayer Cross Counting, JGAA, 8(2) 179–194 (2004)
 */
var bilayerCrossCount = dagre.layout.order.bilayerCrossCount = function(g, layer1, layer2) {
  var layer2Pos = layerPos(layer2);

  var indices = [];
  layer1.forEach(function(u) {
    var nodeIndices = [];
    g.outEdges(u).forEach(function(e) { nodeIndices.push(layer2Pos[g.target(e)]); });
    nodeIndices.sort(function(x, y) { return x - y; });
    indices = indices.concat(nodeIndices);
  });

  var firstIndex = 1;
  while (firstIndex < layer2.length) firstIndex <<= 1;

  var treeSize = 2 * firstIndex - 1;
  firstIndex -= 1;

  var tree = [];
  for (var i = 0; i < treeSize; ++i) { tree[i] = 0; }

  var cc = 0;
  indices.forEach(function(i) {
    var treeIndex = i + firstIndex;
    ++tree[treeIndex];
    var weightSum = 0;
    while (treeIndex > 0) {
      if (treeIndex % 2) {
        cc += tree[treeIndex + 1];
      }
      treeIndex = (treeIndex - 1) >> 1;
      ++tree[treeIndex];
    }
  });

  return cc;
}

function layerPos(layer) {
  var pos = {};
  layer.forEach(function(u, i) { pos[u] = i; });
  return pos;
}
