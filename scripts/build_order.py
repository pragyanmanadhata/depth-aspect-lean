"""Read the project's internal imports and order modules dependency first."""
from pathlib import Path
import re


def module_build_order(paths: list[Path]) -> list[str]:
    sources = {'DepthAspect.' + path.stem: path for path in paths}
    dependencies = {}
    for name, path in sources.items():
        imports = re.findall(r'^import (\S+)\s*$', path.read_text(), re.M)
        dependencies[name] = {item for item in imports if item.startswith('DepthAspect.')}
        missing = dependencies[name] - sources.keys()
        if missing:
            raise ValueError(f'{name} imports missing project modules: {sorted(missing)}')

    order, done, active = [], set(), set()

    def visit(name):
        if name in done:
            return
        if name in active:
            raise ValueError(f'Project import cycle includes {name}')
        active.add(name)
        for dependency in sorted(dependencies[name]):
            visit(dependency)
        active.remove(name)
        done.add(name)
        order.append(name)

    for name in sorted(sources):
        visit(name)
    return order
