"""Project modules, exact import dependencies, and common verification flags."""

load("@lean_imports//:imports.bzl", "IMPORTS")
load("@rules_lean//lean:defs.bzl", "lean_library")

_LEAN_FLAGS = [
    "-Dpp.unicode.fun=true",
    "-DrelaxedAutoImplicit=false",
    "-Dweak.linter.mathlibStandardSet=true",
    "-DmaxSynthPendingDepth=3",
]

_EXTERNAL_REPOS = {
    "Architect": "LeanArchitect",
    "PrimeNumberTheoremAnd": "PrimeNumberTheoremAnd",
    "Mathlib": "mathlib",
    "Batteries": "mathlib",
    "Aesop": "mathlib",
    "Qq": "mathlib",
    "Plausible": "mathlib",
    "LeanSearchClient": "mathlib",
    "ProofWidgets": "mathlib",
    "ImportGraph": "mathlib",
}

def _is_project_package(package):
    return not package or package == "RiemannResearch" or package.startswith("RiemannResearch/")

def _module_name(package, local):
    return (package.replace("/", ".") + "." if package else "") + local

def _target_name(package, local):
    # Reserve the root name for the full-project aggregate.
    return "RiemannResearch_module" if not package and local == "RiemannResearch" else local

def _project_labels():
    return {
        _module_name(package, local): "//%s:%s" % (package, _target_name(package, local))
        for package, modules in IMPORTS.items()
        if _is_project_package(package)
        for local in modules
    }

_PROJECT_LABELS = _project_labels()

def _dependency(module):
    namespace = module.partition(".")[0]
    if namespace in ["Init", "Lean", "Std", "Lake"]:
        return None
    if module in _PROJECT_LABELS:
        return _PROJECT_LABELS[module]
    if namespace in _EXTERNAL_REPOS:
        return "@%s//:%s" % (_EXTERNAL_REPOS[namespace], module)
    fail("No Bazel dependency for Lean import %s" % module)

def lean_modules():
    """One target per source, including descendants without their own BUILD."""
    package = native.package_name()
    imports = IMPORTS.get(package, {})
    targets = []
    for source in native.glob(["**/*.lean"], allow_empty = True):
        local = source[:-len(".lean")].replace("/", ".")
        if local not in imports:
            fail("Missing import index for %s/%s" % (package, source))
        name = _target_name(package, local)
        deps = {}
        for module in imports[local]:
            label = _dependency(module)
            if label:
                deps[label] = True
        lean_library(
            name = name,
            srcs = [source],
            deps = sorted(deps),
            module_prefix = package,
            extra_flags = _LEAN_FLAGS,
            forbid_sorry = True,
            visibility = ["//visibility:public"],
        )
        targets.append(":" + name)
    native.filegroup(
        name = "modules",
        srcs = targets,
        visibility = ["//visibility:public"],
    )

def lean_project():
    """Compile every project source, including modules absent from the root import file."""
    lean_modules()
    native.filegroup(
        name = "RiemannResearch",
        srcs = [
            "//%s:modules" % package
            for package in sorted(IMPORTS)
            if _is_project_package(package)
        ],
        visibility = ["//visibility:public"],
    )
