// var dad = {};
// __addProperty__(dad);
// console.log(dad['son']);
// "1"

// ======== single layer with LdaKeyedProperty
// function onLoad(options) {
//   var keyname = "foo";
//   options[keyname] = options[keyname] + 'test';
//   console.log(options[keyname]);
// }
// var options = { 'fakeKey': 'fakeValue' };
// onLoad(options);
// ========


// ======== set taint to new property value with LdaKeyedProperty
// function onLoad(options) {
//   var keyname = "foo";
//   console.log('===', options[keyname]);
//   var c = options[keyname].__getTaint__()
//   var b = new Uint8Array(c);
//   console.log('===', b);

//   options[keyname] = options[keyname] + 'test';
//   console.log('===', options[keyname]);
//   var c = options[keyname].__getTaint__()
//   var b = new Uint8Array(c);
//   console.log('===', b);

// }
// var options = { 'fakeKey': 'fakeValue' };
// __setTaint__(options, 1);
// var c = options['fakeKey'].__getTaint__()
// var b = new Uint8Array(c);
// console.log('===', b);
// onLoad(options);
// ========


// ======== single layer with LdaNamedProperty
// function onLoad(options) {
//   console.log('===', options["foo"]);
//   var c = options["foo"].__getTaint__()
//   var b = new Uint8Array(c);
//   console.log('===', b);
// }
// var options = { 'fakeKey': 'fakeValue' };
// __setTaint__(options, 1);
// onLoad(options);
// ========

// ======== set taint to new property value with LdaNamedProperty
// function onLoad(options) {
//   console.log('===fakeValue', options["foo"]);
//   var c = options["foo"].__getTaint__()
//   var b = new Uint8Array(c);
//   console.log('===111111111', b);

//   options["foo"] = options["foo"] + 'test';
//   console.log('===fakeValuetest', options["foo"]);
//   var c = options["foo"].__getTaint__()
//   var b = new Uint8Array(c);
//   console.log('===1111111110000', b);

// }
// var options = { 'fakeKey': 'fakeValue' };
// __setTaint__(options, 1);
// var c = options['fakeKey'].__getTaint__()
// var b = new Uint8Array(c);
// console.log('===111111111', b);
// onLoad(options);
// ========




// === multiple layers of property access of an object, we assume it to be a string
// var happy = "fakeValue";

// // normally it will output undefined,
// // but if typeof (a === "string" && a == "fakeValue")
// // -> change a to an object: happy = { "fakeKey": "fakeValue", "foo": "fakeValue" }
// // this will output: fakeValue
// console.log(happy.foo); // recv type is string
// console.log(JSON.stringify(happy));

// // this will output: fakeValue
// // because it will check if happy has a fakeKey and the value is fakeValue
// // happy = { "fakeKey": "fakeValue", "foo": "fakeValue" }
// console.log(happy.cuck);
// console.log(JSON.stringify(happy));

// // this will output: fakeValue
// // because it will check if happy.foo is string "fakeValue"
// console.log(happy.foo.c);
// console.log(JSON.stringify(happy));

// var happy = "fakeValue";
// // step1: happy = { "fakeKey": "fakeValue", "nice": "fakeValue" }
// // step2: happy = { "fakeKey": "fakeValue", "nice": {"suzy":"fakeValue", "fakeKey":"fakeValue"} }
// console.log(happy.nice.suzy);
// console.log(JSON.stringify(happy));

// this should output: {"fakeKey":"fakeValue","foo":"fakeValue"}
// no, because we don't really change happy, we change the return value of its property access instead
// console.log(JSON.stringify(happy));

// again the since a.foo is string and a.foo == "fakeValue", we change a.foo to an object
// now a = { "fakeKey": "fakeValue", "foo": "fakeValue" }
// this will output: fakeValue
// console.log(happy.foo.c);

// we can not do multiple layer in this way
// var options = { 'fakeKey': 'fakeValue' };
// // {'fakeKey': 'fakeValue', 'foo': 'fakeValue'};
// console.log(options.foo); // recv type is object
// console.log(options.foo.c);
// console.log(options.suzy); // recv type is object
// console.log(JSON.stringify(options));
// drawback: we don't know if it's an array or number


// we can not do multiple layer in this way
// var options = { 'fakeKey': 'fakeValue' };
// // {'fakeKey': 'fakeValue', 'foo': 'fakeValue'};
// var keyname = "foo";
// console.log(options[keyname]); // recv type is object
// var secKeyname = "c";
// console.log(options[keyname][secKeyname]);
// var anotherKeyname = "suzy";
// console.log(options[anotherKeyname]); // recv type is object
// console.log(JSON.stringify(options));
// drawback: we don't know if it's an array or number

var options = { 'fakeKey': 'fakeValue' }; // { 'testkey': 'testvalue' } can be seen as an empty object
// __setTaint__(options, __taintConstants__()['OnLaunch']);
// __setTaint__(options, 1);
__setTaint__(options, 3);
// console.log(new Uint8Array(options.__getTaint__(1))[0]);
%DebugPrint(options);
console.log(options.a)
// now: options = {"testkey":"testvalue","a":"testvalue"}
// expect: options = { 'testkey': 'testvalue', 'a':{'testkey': 'testvalue'}};
console.log(JSON.stringify(options))
console.log(new Uint8Array(options.a.fakeKey.__getTaint__(1))[0]);
console.log(options.a.b)
// options = { 'testkey': 'testvalue', 'a':{'testkey': 'testvalue', 'b':{'testkey': 'testvalue'}}};
console.log(JSON.stringify(options))
console.log(new Uint8Array(options.a.b.fakeKey.__getTaint__(1))[0]);
// ==============


// var options = 'testvalue';
// __setTaint__(options, 3);
// console.log(new Uint8Array(options.__getTaint__(1))[0]);
// console.log(options.a)
// console.log(options.a.b)
