@[extern "lean_allocator_diagnostic_probe"]
opaque leanAllocatorDiagnosticProbe : IO UInt32

def main : IO UInt32 := leanAllocatorDiagnosticProbe
