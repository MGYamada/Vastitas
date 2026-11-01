@[extern "allocation_capability_probe"]
opaque allocationCapabilityProbe : IO UInt32

def main : IO UInt32 := allocationCapabilityProbe
