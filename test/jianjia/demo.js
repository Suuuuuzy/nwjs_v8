
// ======
function onLoad(options) {
  var keyname = "foo";
  // options[keyname] = options[keyname] + 'test';
  console.log(options[keyname]);
  console.log(JSON.stringify(options))

  console.log(options.a);
  console.log(JSON.stringify(options))

  console.log(options.a.b);
  console.log(new Uint8Array(options.a.b.fakeKey.__getTaint__()));
  console.log(JSON.stringify(options))

}
var options = {}; // { 'testkey': 'testvalue' } can be seen as an empty object
Object.defineProperty(options, 'fakeKey', {
  value: 'fakeValue',
  enumerable: false
});
__setTaint__(options, 4)
onLoad(options);
// ======


// ======
// var a = 'fakeValue';
// a.__setTaint__(1);
// console.log(new Uint8Array(a.__getTaint__()));
// console.log(a.b)
// console.log(a.b.c)
//  ======
