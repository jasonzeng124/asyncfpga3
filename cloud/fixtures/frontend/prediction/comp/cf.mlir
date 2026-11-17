module {
  memref.global "private" constant @".str" : memref<10xi8> = dense<[91, 55, 46, 48, 44, 55, 46, 53, 93, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.2" : memref<6xi8> = dense<[102, 108, 111, 97, 116, 0]> {alignment = 1 : i64}
  func.func @prediction(%arg0: memref<100xf32>, %arg1: memref<100xf32>, %arg2: f32) {
    %c0_i32 = arith.constant 0 : i32
    %cst = arith.constant 1.000000e+00 : f32
    %cst_0 = arith.constant 1.000000e+01 : f32
    %c100_i32 = arith.constant 100 : i32
    %cst_1 = arith.constant 5.000000e+00 : f32
    %c1_i32 = arith.constant 1 : i32
    %0 = memref.get_global @".str" : memref<10xi8>
    %1 = memref.get_global @".str.1" : memref<6xi8>
    %2 = memref.get_global @".str.2" : memref<6xi8>
    %3 = memref.get_global @".str" : memref<10xi8>
    %4 = memref.get_global @".str.1" : memref<6xi8>
    %5 = memref.get_global @".str.2" : memref<6xi8>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%6: i32):  // 2 preds: ^bb0, ^bb1
    %7 = arith.extui %6 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<100xf32>
    %10 = arith.addf %9, %cst : f32
    %11 = arith.mulf %10, %cst_0 : f32
    %12 = arith.fptosi %11 : f32 to i32
    %13 = arith.cmpi eq, %12, %c100_i32 : i32
    %14 = arith.select %13, %cst_1, %9 : f32
    %15 = "dynamatic.prediction_marker"(%14) {dynamatic.predict = {location = "start", marker = 0 : i32, type = "float", values = "[7.0,7.5]"}} : (f32) -> f32
    %16 = arith.addf %15, %arg2 : f32
    %17 = arith.mulf %16, %cst_0 : f32
    %18 = arith.extui %6 : i32 to i64
    %19 = arith.index_cast %18 : i64 to index
    memref.store %17, %arg1[%19] {handshake.name = "store1"} : memref<100xf32>
    %20 = "dynamatic.prediction_marker"(%15) {dynamatic.predict = {location = "start", marker = 1 : i32, type = "float", values = "[7.0,7.5]"}} : (f32) -> f32
    %21 = arith.subf %20, %arg2 : f32
    %22 = arith.mulf %21, %cst_0 : f32
    %23 = arith.extui %6 : i32 to i64
    %24 = arith.index_cast %23 : i64 to index
    memref.store %22, %arg0[%24] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<100xf32>
    %25 = arith.addi %6, %c1_i32 : i32
    %26 = arith.cmpi ult, %25, %c100_i32 : i32
    cf.cond_br %26, ^bb1(%25 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    return
  }
}
