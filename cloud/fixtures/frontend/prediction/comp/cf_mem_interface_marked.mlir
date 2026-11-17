module {
  memref.global "private" constant @".str" : memref<10xi8> = dense<[91, 55, 46, 48, 44, 55, 46, 53, 93, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64, handshake.name = "global1"}
  memref.global "private" constant @".str.2" : memref<6xi8> = dense<[102, 108, 111, 97, 116, 0]> {alignment = 1 : i64, handshake.name = "global2"}
  func.func @prediction(%arg0: memref<100xf32> {handshake.arg_name = "a"}, %arg1: memref<100xf32> {handshake.arg_name = "b"}, %arg2: f32 {handshake.arg_name = "c"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant6"} 1 : i32
    %cst = arith.constant {handshake.name = "constant7"} 5.000000e+00 : f32
    %c100_i32 = arith.constant {handshake.name = "constant8"} 100 : i32
    %cst_0 = arith.constant {handshake.name = "constant9"} 1.000000e+01 : f32
    %cst_1 = arith.constant {handshake.name = "constant10"} 1.000000e+00 : f32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : memref<100xf32>
    %4 = arith.addf %3, %cst_1 {handshake.name = "addf0"} : f32
    %5 = arith.mulf %4, %cst_0 {handshake.name = "mulf0"} : f32
    %6 = arith.fptosi %5 {handshake.name = "fptosi0"} : f32 to i32
    %7 = arith.cmpi eq, %6, %c100_i32 {handshake.name = "cmpi0"} : i32
    %8 = arith.select %7, %cst, %3 {dynamatic.predict = {location = "start", marker = 1 : i32, type = "float", values = "[7.0,7.5]"}, dynamatic.predict.result_idx = 0 : i32, handshake.name = "select0"} : f32
    %9 = arith.addf %8, %arg2 {handshake.name = "addf1"} : f32
    %10 = arith.mulf %9, %cst_0 {handshake.name = "mulf1"} : f32
    %11 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %12 = arith.index_cast %11 {handshake.name = "index_cast1"} : i64 to index
    memref.store %10, %arg1[%12] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : memref<100xf32>
    %13 = arith.subf %8, %arg2 {handshake.name = "subf0"} : f32
    %14 = arith.mulf %13, %cst_0 {handshake.name = "mulf2"} : f32
    %15 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast2"} : i64 to index
    memref.store %14, %arg0[%16] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : memref<100xf32>
    %17 = arith.addi %0, %c1_i32 {handshake.name = "addi0"} : i32
    %18 = arith.cmpi ult, %17, %c100_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %18, ^bb1(%17 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    return {handshake.name = "return0"}
  }
}

