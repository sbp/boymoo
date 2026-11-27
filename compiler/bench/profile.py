"""Attributes the samples of the reports of sample(1), of macOS, to the
labels of an executable that the many-pass compiler writes;
compiler/bench/profile.sh runs it.

    python3 compiler/bench/profile.py [--skip LABEL] LABELS NAME SAMPLE ...

LABELS has one line "OFFSET LABEL" for each label, the offset counted from
the start of the code, which is at offset 4096 of the file. NAME is the
name of the executable as the reports give it. Each sample taken with the
program counter in the executable counts for the label at or before it.
With --skip, the samples at LABEL are left out of the shares: sys:read,
for example, where the executable waits for its input to start.
"""
import bisect
import re
import sys

CODE_START = 0x1000
LINE = re.compile(r'^(\s*)(\d+) (.*)$')
FRAME = re.compile(r'\(in (\S+)\)\s+load address 0x[0-9a-f]+ \+ 0x([0-9a-f]+)')


def read_labels(path):
    offsets, names = [], []
    for line in open(path):
        parts = line.split(None, 1)
        if len(parts) == 2 and parts[0].isdigit():
            offsets.append(int(parts[0]))
            names.append(parts[1].strip())
    return offsets, names


def self_samples(path):
    """Yields (FRAME, COUNT): COUNT samples had FRAME at the top of the
    stack, the count of its node of the call graph less those of its
    children."""
    nodes = []  # (indent, count, frame)
    started = False
    for line in open(path):
        if line.startswith('Call graph:'):
            started = True
            continue
        if not started:
            continue
        if not line.strip():
            if nodes:
                break
            continue
        m = LINE.match(line.rstrip('\n'))
        if not m:
            continue
        nodes.append((len(m.group(1)), int(m.group(2)), m.group(3)))
    for i, (indent, count, frame) in enumerate(nodes):
        # The children of a node are the nodes below it, up to the next
        # node no deeper than it, that have the least greater indent.
        j = i + 1
        while j < len(nodes) and nodes[j][0] > indent:
            j += 1
        children = 0
        if j > i + 1:
            child_indent = nodes[i + 1][0]
            children = sum(n[1] for n in nodes[i + 1:j] if n[0] == child_indent)
        own = count - children
        if own > 0:
            yield frame, own


def group(label):
    for prefix in ('prim:', 'jet:', 'sys:', 'os:'):
        if label.startswith(prefix):
            return label
    if label.startswith('rt:'):
        for family, words in (('collector', ('rt:collect', 'rt:scan', 'rt:forward',
                                             'rt:release', 'rt:sweep')),
                              ('allocation', ('rt:alloc', 'rt:new-', 'rt:map-string')),
                              ('stacks', ('rt:grow', 'rt:ensure-stack', 'rt:deep')),
                              ('integers', ('rt:z-',)),
                              ('rationals', ('rt:q-', 'rt:num-'))):
            if label.startswith(words):
                return 'rt: ' + family
        return 'rt: other (' + label + ')'
    return 'compiled code'


def main():
    args = sys.argv[1:]
    skip = None
    if args[0] == '--skip':
        skip, args = args[1], args[2:]
    offsets, names = read_labels(args[0])
    exe = args[1]
    by_label, total, outside = {}, 0, 0
    for path in args[2:]:
        for frame, count in self_samples(path):
            total += count
            m = FRAME.search(frame)
            if not m or m.group(1) != exe:
                outside += count
                continue
            off = int(m.group(2), 16) - CODE_START
            i = bisect.bisect_right(offsets, off) - 1
            label = names[i] if i >= 0 else '(before the code)'
            by_label[label] = by_label.get(label, 0) + count
    if skip in by_label:
        print('left out: %d samples at %s' % (by_label.pop(skip), skip))
        total = sum(by_label.values()) + outside
    groups = {}
    for label, count in by_label.items():
        g = group(label)
        groups[g] = groups.get(g, 0) + count
    print('samples: %d, outside the executable: %d' % (total, outside))
    print('\nby part:')
    for g, c in sorted(groups.items(), key=lambda x: -x[1]):
        print('%7d %5.1f%%  %s' % (c, 100.0 * c / max(total, 1), g))
    print('\nby label (first 40):')
    for label, c in sorted(by_label.items(), key=lambda x: -x[1])[:40]:
        print('%7d %5.1f%%  %s' % (c, 100.0 * c / max(total, 1), label))


main()
