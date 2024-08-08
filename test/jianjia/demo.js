
// ======
// function onLoad(options) {
//   var keyname = "foo";
//   // options[keyname] = options[keyname] + 'test';
//   console.log(options[keyname]);
//   console.log(JSON.stringify(options))

//   console.log(options.a);
//   console.log(JSON.stringify(options))

//   console.log(options.a.b);
//   console.log(new Uint8Array(options.a.b.fakeKey.__getTaint__()));
//   console.log(JSON.stringify(options))

// }
// var options = {}; // { 'testkey': 'testvalue' } can be seen as an empty object
// Object.defineProperty(options, 'fakeKey', {
//   value: 'fakeValue',
//   enumerable: false
// });
// __setTaint__(options, 4)
// onLoad(options);
// ======


// ======
// var a = 'fakeValue';
// a.__setTaint__(1);
// console.log(new Uint8Array(new Uint8Array(a.__getTaint__())));
// console.log(a.b);
// console.log(new Uint8Array(a.b.c.__getTaint__()));
//  ======

//  ======
// var r = { "appLaunchInfo": { "query": {} } };
// r["appLaunchInfo"]["query"] = {"testkey":"testvalue"};
// __setTaint__(r["appLaunchInfo"]["query"], __taintConstants__()['OnLaunch']);
//  ======


// ====== case 23, this works when we pass testvalue and use it
// var b = 'testvalue1'
// b.__setTaint__(3) // this will fail
// console.log(new Uint8Array(b.__getTaint__()));
//   console.log(b.sfgs);
// var c = 'testvalue12';
// console.log(new Uint8Array(c.__getTaint__()));
// c.__setTaint__(2);
// console.log(c.vfd.s)
  // console.log(b === c)
// once one string is tainted, all the same other strings are tainted
// this is caused by the nature of how v8 store strings
// or, we set another string value to be automatically generating properties, but not tainted
// that means we have two categories of strings that can generate properties,
// one is tainted, the other is not tainted
// testkey is not tainted, but can generate properties
// {testkey: testvalue}
// we only taint the value, not the key
// so if we only want to generate propertie
// ======


//
a = { testkey: 'testvalue_id' }
a.testkey.__setTaint__(5)
var v = 'newjianjis';
console.log(a[v].testkey)
console.log(a.id)
console.log(a.c.g)
console.log(JSON.stringify(a))
console.log(new Uint8Array(a.c.g.testkey.__getTaint__()))

// b = { testkey: 'testvalue_2' }
// var c = 'jainjia';
// console.log(new Uint8Array(b[c].g.testkey.__getTaint__()))
