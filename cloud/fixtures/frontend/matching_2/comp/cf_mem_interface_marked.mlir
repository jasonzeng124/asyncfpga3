module {
  func.func @matching_2(%arg0: memref<1000xi32> {handshake.arg_name = "edges"}, %arg1: memref<1000xf32> {handshake.arg_name = "vertices"}, %arg2: i32 {handshake.arg_name = "num_edges"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg2, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32 : i32), ^bb5 {handshake.name = "cond_br0"}
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb4
    %cst = arith.constant {handshake.name = "constant3"} 0.000000e+00 : f32
    %c1_i32 = arith.constant {handshake.name = "constant4"} 1 : i32
    %2 = arith.shli %1, %c1_i32 {handshake.name = "shli0"} : i32
    %3 = arith.extui %2 {handshake.name = "extui0"} : i32 to i64
    %4 = arith.index_cast %3 {handshake.name = "index_cast0"} : i64 to index
    %5 = memref.load %arg0[%4] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<1000xi32>
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i32 to index
    %7 = memref.load %arg1[%6] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : memref<1000xf32>
    %8 = arith.cmpf olt, %7, %cst {handshake.name = "cmpf0"} : f32
    cf.cond_br %8, ^bb2, ^bb4 {handshake.name = "cond_br1"}
  ^bb2:  // pred: ^bb1
    %cst_0 = arith.constant {handshake.name = "constant5"} 0.000000e+00 : f32
    %c1_i32_1 = arith.constant {handshake.name = "constant6"} 1 : i32
    %9 = arith.ori %2, %c1_i32_1 {handshake.name = "ori0"} : i32
    %10 = arith.extui %9 {handshake.name = "extui1"} : i32 to i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast2"} : i64 to index
    %12 = memref.load %arg0[%11] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : memref<1000xi32>
    %13 = arith.index_cast %12 {handshake.name = "index_cast3"} : i32 to index
    %14 = memref.load %arg1[%13] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load3"} : memref<1000xf32>
    %15 = arith.cmpf olt, %14, %cst_0 {handshake.name = "cmpf1"} : f32
    cf.cond_br %15, ^bb3, ^bb4 {handshake.name = "cond_br2"}
  ^bb3:  // pred: ^bb2
    %16 = arith.sitofp %12 {handshake.name = "sitofp0"} : i32 to f32
    %17 = arith.index_cast %5 {handshake.name = "index_cast4"} : i32 to index
    memref.store %16, %arg1[%17] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store4"} : memref<1000xf32>
    %18 = arith.sitofp %5 {handshake.name = "sitofp1"} : i32 to f32
    %19 = arith.index_cast %12 {handshake.name = "index_cast5"} : i32 to index
    memref.store %18, %arg1[%19] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store5"} : memref<1000xf32>
    cf.br ^bb4 {handshake.name = "br0"}
  ^bb4:  // 3 preds: ^bb1, ^bb2, ^bb3
    %c1_i32_2 = arith.constant {handshake.name = "constant7"} 1 : i32
    %20 = arith.addi %1, %c1_i32_2 {handshake.name = "addi0"} : i32
    %21 = arith.cmpi slt, %20, %arg2 {handshake.name = "cmpi1"} : i32
    cf.cond_br %21, ^bb1(%20 : i32), ^bb5 {handshake.name = "cond_br3"}
  ^bb5:  // 2 preds: ^bb0, ^bb4
    return {handshake.name = "return0"}
  }
}

