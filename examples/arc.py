"""Print the paper's n points and the measured range of distances per index gap."""

import argparse
import math


def norm(x, y):
    return max(
        math.hypot(x, y),
        math.hypot(math.sqrt(4 / 5) * x, math.sqrt(6 / 5) * y),
        4 / 5 * abs(x + y),
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, help="number of points (at least four)")
    args = parser.parse_args()
    if args.n < 4:
        parser.error("n must be at least four")
    h = math.pi / (1000 * args.n)
    points = [(-math.sin(j * h), math.cos(j * h)) for j in range(1, args.n + 1)]
    print("index  x  y")
    for j, (x, y) in enumerate(points, 1):
        print(j, format(x, ".16g"), format(y, ".16g"))
    print("\ngap  pairs  minimum_distance  maximum_distance  chord_formula")
    for gap in range(1, args.n):
        lengths = [norm(u - x, v - y) for (x, y), (u, v) in zip(points, points[gap:])]
        print(
            gap,
            len(lengths),
            format(min(lengths), ".16g"),
            format(max(lengths), ".16g"),
            format(2 * math.sin(gap * h / 2), ".16g"),
        )


if __name__ == "__main__":
    main()
