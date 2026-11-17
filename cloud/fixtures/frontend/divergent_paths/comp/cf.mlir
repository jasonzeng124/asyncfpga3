module {
  memref.global "private" constant @".str" : memref<4xi8> = dense<[91, 55, 93, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.2" : memref<4xi8> = dense<[105, 110, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.3" : memref<1xi8> = dense<0> {alignment = 1 : i64}
  memref.global "private" constant @".str.4" : memref<4xi8> = dense<[101, 110, 100, 0]> {alignment = 1 : i64}
  func.func @divergent_paths(%arg0: memref<100xi32>, %arg1: memref<100xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c3_i32 = arith.constant 3 : i32
    %c255_i32 = arith.constant 255 : i32
    %c2_i32 = arith.constant 2 : i32
    %c1_i32 = arith.constant 1 : i32
    %c100_i32 = arith.constant 100 : i32
    %0 = memref.get_global @".str" : memref<4xi8>
    %1 = memref.get_global @".str.1" : memref<6xi8>
    %2 = memref.get_global @".str.2" : memref<4xi8>
    %3 = memref.get_global @".str.3" : memref<1xi8>
    %4 = memref.get_global @".str.4" : memref<4xi8>
    %5 = memref.get_global @".str.3" : memref<1xi8>
    %6 = memref.get_global @".str.3" : memref<1xi8>
    %7 = memref.get_global @".str.4" : memref<4xi8>
    %8 = memref.get_global @".str.3" : memref<1xi8>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%9: i32):  // 2 preds: ^bb0, ^bb1
    %10 = arith.extui %9 : i32 to i64
    %11 = arith.index_cast %10 : i64 to index
    %12 = memref.load %arg0[%11] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<100xi32>
    %13 = "dynamatic.prediction_marker"(%12) {dynamatic.predict = {location = "start", marker = 3 : i32, type = "int", values = "[7]"}} : (i32) -> i32
    %14 = arith.xori %13, %c255_i32 : i32
    %15 = arith.addi %14, %c2_i32 : i32
    %16 = "dynamatic.prediction_marker"(%15) {dynamatic.predict = {location = "end", marker = 3 : i32, type = "", values = ""}} : (i32) -> i32
    %17 = arith.muli %14, %c3_i32 : i32
    %18 = "dynamatic.prediction_marker"(%17) {dynamatic.predict = {location = "end", marker = 3 : i32, type = "", values = ""}} : (i32) -> i32
    %19 = arith.extui %9 : i32 to i64
    %20 = arith.index_cast %19 : i64 to index
    memref.store %16, %arg0[%20] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<100xi32>
    %21 = arith.extui %9 : i32 to i64
    %22 = arith.index_cast %21 : i64 to index
    memref.store %18, %arg1[%22] {handshake.name = "store2"} : memref<100xi32>
    %23 = arith.addi %9, %c1_i32 : i32
    %24 = arith.cmpi ult, %23, %c100_i32 : i32
    cf.cond_br %24, ^bb1(%23 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    return
  }
}
