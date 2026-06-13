from .dregg import *  # noqa: F401,F403
from . import dregg as _native

__doc__ = _native.__doc__
if hasattr(_native, "__all__"):
    __all__ = _native.__all__

# The pyo3 submodules (`dregg.program`, `dregg.deploy`) register themselves in
# `sys.modules` at import time (see the `#[pymodule]` body), so
# `import dregg.program` / `import dregg.deploy` resolve without re-export here.
