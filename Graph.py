
# ecmaspeak-py/Graph.py:
# Create a dependency-graph, and find its strongly connected components.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys
from collections import defaultdict

from shared import stderr

class Graph:
    def __init__(self):
        self.vertices = set()
        self.arcs_from_ = defaultdict(set)

    def add_vertex(self, vertex):
        self.vertices.add(vertex)

    def add_arc(self, src_vertex, dst_vertex):
        self.add_vertex(src_vertex)
        self.add_vertex(dst_vertex)
        self.arcs_from_[src_vertex].add(dst_vertex)

    def print_arcs(self, file=sys.stdout, indent=''):
        for (src_vertex, dst_vertices) in sorted(self.arcs_from_.items()):
            for dst_vertex in sorted(list(dst_vertices)):
                print('%s%s -> %s' % (indent, src_vertex, dst_vertex), file=file)

    def compute_dependency_levels(self):

        self.find_strongly_connected_components()

        stderr( '    %d SCCs' % len(cluster_) )

        stderr( "    sorting..." )
        for cluster in cluster_:
            cluster.members.sort()
            # cluster.position = vertex_collater(cluster.members[0])

        stderr( "    dependencies between SCCs..." )
        for cluster in cluster_:
            cluster.contains_a_cycle = False
            for vertex in cluster.members:
                for p in self.arcs_from_[vertex]:
                    if self.cluster_for_[p] is cluster:
                        # a "sideways" dependency
                        cluster.contains_a_cycle = True
                    else:
                        if self.cluster_for_[p] not in cluster.direct_prereqs:
                            cluster.direct_prereqs.append(self.cluster_for_[p])

            if len(cluster.members)>1:
                assert cluster.contains_a_cycle
            # If len(cluster.members) == 1, it still might contain a cycle

        levels = establish_dependency_levels()

        return levels

    # --------

    def find_strongly_connected_components(self):
        # Find the strongly connected components of the dependency graph.
        # See 'Path-based strong component algorithm' in wikipedia

        self.preorder_number_of_ = {}
        self.cluster_for_ = {}

        class G: pass
        g = G()

        g.S = []
        # all the vertices [seen so far] that have not yet been assigned to a SCC,
        # in the order in which the depth-first search reaches the vertices

        g.P = []
        # vertices that have not yet been determined to belong to different SCCs from each other.

        g.C = 0

        def rec_search(v):
            assert v in self.vertices
            assert v not in self.preorder_number_of_

            # 1. Set the preorder number of v to C, and increment C.
            self.preorder_number_of_[v] = g.C
            g.C += 1

            # 2. Push v onto S and also onto P.
            g.S.append(v)
            g.P.append(v)

            # 3. For each edge from v to a neighboring vertex w:
            for w in self.arcs_from_[v]:
                # If the preorder number of w has not yet been assigned,
                # recursively search w;
                if w not in self.preorder_number_of_:
                    rec_search(w)
                # Otherwise, if w has not yet been assigned to
                # a strongly connected component:
                elif w in g.S:
                    # Repeatedly pop vertices from P until the top element of P has a
                    # preorder number less than or equal to the preorder number of w.
                    while self.preorder_number_of_[g.P[-1]] > self.preorder_number_of_[w]:
                        g.P.pop()

            # 4. If v is the top element of P:
            if v is g.P[-1]:
                # Pop vertices from S until v has been popped,
                # and assign the popped vertices to a new component.
                scc = Cluster()
                while True:
                    w = g.S.pop()
                    # scc.add(w)
                    assert w not in self.cluster_for_
                    self.cluster_for_[w] = scc
                    scc.members.append(w)
                    if w is v: break

                # Pop v from P.
                w = g.P.pop()
                assert w is v

        for v in self.vertices:
            if v not in self.preorder_number_of_:
                rec_search(v)

# -----------------

cluster_ = []

class Cluster:
    def __init__(self):
        self.number = len(cluster_)
        self.members = []
        self.direct_prereqs = []
        cluster_.append(self)

# ------------------------------------------------------------------------------

def establish_dependency_levels():
    stderr( "    establish_dependency_levels ..." )

    levels = []

    def get_level_of_cluster(cluster):
        if hasattr(cluster, 'level'):
            return cluster.level

        if len(cluster.direct_prereqs) == 0:
            # only depends on predefineds
            level = 0
        else:
            level = 1 + max(
                get_level_of_cluster(prereq)
                for prereq in cluster.direct_prereqs
            )
        cluster.level = level

        if level < len(levels):
            pass
        elif level == len(levels):
            levels.append([])
        else:
            assert 0
        levels[level].append(cluster)

    for cluster in cluster_:
        get_level_of_cluster(cluster)

    stderr( "    %d levels" % len(levels) )

    for (L, clusters_on_level_L) in enumerate(levels):
        clusters_on_level_L.sort(key = lambda cluster: cluster.members[0])

    return levels

# vim: sw=4 ts=4 expandtab
