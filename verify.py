"""Exact finite checks for the tree exchange inequalities. Standard Python 3."""

from collections import defaultdict
from itertools import combinations, product


def tree_distances(code):
    """Decode a Pruefer sequence and compute all path lengths."""
    n = len(code) + 2
    degree = [1 + code.count(i) for i in range(n)]
    edges = []
    for parent in code:
        leaf = next(i for i in range(n) if degree[i] == 1)
        edges.append((leaf, parent))
        degree[leaf] -= 1
        degree[parent] -= 1
    edges.append(tuple(i for i in range(n) if degree[i] == 1))
    adj = [[] for _ in range(n)]
    for u, v in edges:
        length = 1 + (u + v) % 3
        adj[u].append((v, length))
        adj[v].append((u, length))
    dist = [[0] * n for _ in range(n)]
    for start in range(n):
        stack = [(start, -1)]
        while stack:
            u, parent = stack.pop()
            for v, length in adj[u]:
                if v != parent:
                    dist[start][v] = dist[start][u] + length
                    stack.append((v, u))
    return dist


def cost(dist, base, load):
    return sum((base[i] + load[i]) * (base[j] + load[j]) * dist[i][j]
               for i, j in combinations(range(len(base)), 2))


def swap(load, i, j):
    changed = list(load)
    changed[i], changed[j] = changed[j], changed[i]
    return tuple(changed)


def check_tree(dist):
    n = len(dist)
    base = [1 + i % 3 for i in range(n)]
    values = {s: cost(dist, base, s) for s in product((0, 1, 3), repeat=n)}
    triples = []
    for x, y in combinations(range(n), 2):
        for z in range(n):
            a, b = dist[x][z], dist[z][y]
            if a and b and a + b == dist[x][y]:
                fiber = [v for v in range(n)
                         if dist[v][x] == dist[v][z] + a
                         and dist[v][y] == dist[v][z] + b]
                triples.append((x, z, y, a, b, fiber))
    extrema = defaultdict(list)
    for s, value in values.items():
        extrema[tuple(sorted(s))].append(value)
    limits = {key: (min(l), max(l)) for key, l in extrema.items()}
    valleys = peaks = 0
    for s, value in values.items():
        lo, hi = limits[tuple(sorted(s))]
        for x, z, y, a, b, fiber in triples:
            if s[z] < min(s[x], s[y]):
                sign = 1
                valleys += 1
                assert value > lo
            elif s[z] > max(s[x], s[y]):
                sign = -1
                peaks += 1
                assert value < hi
            else:
                continue
            p, q = abs(s[x] - s[z]), abs(s[y] - s[z])
            mass = sum(base[v] + s[v] for v in fiber)
            gain = max(sign * (value - values[swap(s, z, i)]) for i in (x, y))
            assert gain * (b*q + a*p) >= a*b*p*q*(2*mass + sign*(p + q))
    return len(values), valleys, peaks


def prefix(sequence):
    result = [0]
    for x in sequence:
        result.append(result[-1] + x)
    return result


def interval_costs(coords, mass, step, width):
    n = len(coords)
    p = prefix(mass)
    px = prefix(v*x for v, x in zip(mass, coords))
    pu = prefix(x*p[i] - px[i] + px[n] - px[i] - x*(p[n] - p[i])
                for i, x in enumerate(coords))
    sx = prefix(coords)
    six = prefix(i*x for i, x in enumerate(coords))
    original = sum(mass[i]*(coords[i]*p[i] - px[i]) for i in range(n))
    for r in range(n - width + 1):
        t = r + width
        within = 2*(six[t]-six[r]) - (r+t-1)*(sx[t]-sx[r])
        yield original + step*(pu[t]-pu[r]) + step**2*within


def check_paths():
    cases = 0
    for n in range(2, 11):
        coords = prefix(1 + (i % 3) for i in range(n - 1))
        dist = [[abs(x-y) for y in coords] for x in coords]
        base = [1 + i % 4 for i in range(n)]
        for k in range(1, n):
            costs = [cost(dist, base, [1 + 3*(i in high) for i in range(n)])
                     for high in combinations(range(n), k)]
            assert min(costs) == min(interval_costs(coords, [b+1 for b in base], 3, k))
            assert max(costs) == max(interval_costs(coords, [b+4 for b in base], -3, n-k))
            cases += 1
    return cases


if __name__ == '__main__':
    trees = assignments = valleys = peaks = 0
    for n in range(2, 6):
        for code in product(range(n), repeat=n-2):
            count, low, high = check_tree(tree_distances(code))
            trees += 1
            assignments += count
            valleys += low
            peaks += high
    print(f'{trees} labelled trees, {assignments} assignments, '
          f'{valleys} valley bounds, {peaks} peak bounds')
    print(f'{check_paths()} binary path instances, both extrema checked')
    star = [[0,1,2,2], [1,0,1,1], [2,1,0,2], [2,1,2,0]]
    for s in [(3,0,3,1), (0,3,0,1)]:
        print('star', s, cost(star, (1,)*4, s),
              cost(star, (1,)*4, swap(s, 0, 1)))
