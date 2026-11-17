module {
  memref.global "private" constant @".str" : memref<4xi8> = dense<[91, 50, 93, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.2" : memref<4xi8> = dense<[105, 110, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.3" : memref<1xi8> = dense<0> {alignment = 1 : i64}
  memref.global "private" constant @".str.4" : memref<4xi8> = dense<[101, 110, 100, 0]> {alignment = 1 : i64}
  func.func @nested_conditionals_1(%arg0: memref<100xi32>, %arg1: i32) {
    %c0_i32 = arith.constant 0 : i32
    %c2_i32 = arith.constant 2 : i32
    %c8_i32 = arith.constant 8 : i32
    %c5_i32 = arith.constant 5 : i32
    %c1_i32 = arith.constant 1 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c3_i32 = arith.constant 3 : i32
    %c100_i32 = arith.constant 100 : i32
    %0 = memref.get_global @".str" : memref<4xi8>
    %1 = memref.get_global @".str.1" : memref<6xi8>
    %2 = memref.get_global @".str.2" : memref<4xi8>
    %3 = memref.get_global @".str.3" : memref<1xi8>
    %4 = memref.get_global @".str.4" : memref<4xi8>
    %5 = memref.get_global @".str.3" : memref<1xi8>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%6: i32):  // 2 preds: ^bb0, ^bb4
    %7 = arith.extui %6 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<100xi32>
    %10 = "dynamatic.prediction_marker"(%9) {dynamatic.predict = {location = "start", marker = 0 : i32, type = "int", values = "[2]"}} : (i32) -> i32
    %11 = arith.addi %10, %c2_i32 : i32
    %12 = arith.cmpi sgt, %10, %c8_i32 : i32
    cf.cond_br %12, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %13 = arith.cmpi sgt, %arg1, %c5_i32 : i32
    %14 = arith.shli %11, %c1_i32 : i32
    %15 = arith.addi %11, %arg1 : i32
    %16 = arith.select %13, %14, %15 : i32
    cf.br ^bb4(%16 : i32)
  ^bb3:  // pred: ^bb1
    %17 = arith.cmpi eq, %arg1, %c0_i32 : i32
    %18 = arith.addi %10, %c-1_i32 : i32
    %19 = arith.muli %11, %arg1 : i32
    %20 = arith.select %17, %18, %19 : i32
    cf.br ^bb4(%20 : i32)
  ^bb4(%21: i32):  // 2 preds: ^bb2, ^bb3
    %22 = arith.addi %21, %c3_i32 : i32
    %23 = "dynamatic.prediction_marker"(%22) {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}} : (i32) -> i32
    %24 = arith.extui %6 : i32 to i64
    %25 = arith.index_cast %24 : i64 to index
    memref.store %23, %arg0[%25] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<100xi32>
    %26 = arith.addi %6, %c1_i32 : i32
    %27 = arith.cmpi ult, %26, %c100_i32 : i32
    cf.cond_br %27, ^bb1(%26 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    return
  }
}
