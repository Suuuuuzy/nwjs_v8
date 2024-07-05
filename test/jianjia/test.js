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
function onLoad(options) {
  console.log('===fakeValue', options["foo"]);
  var c = options["foo"].__getTaint__()
  var b = new Uint8Array(c);
  console.log('===111111111', b);

  options["foo"] = options["foo"] + 'test';
  console.log('===fakeValuetest', options["foo"]);
  var c = options["foo"].__getTaint__()
  var b = new Uint8Array(c);
  console.log('===1111111110000', b);

}
var options = { 'fakeKey': 'fakeValue' };
__setTaint__(options, 1);
var c = options['fakeKey'].__getTaint__()
var b = new Uint8Array(c);
console.log('===111111111', b);
onLoad(options);
// ========



// ======== single layer with LdaNamedPropertyFromSuper
class Parent {
  get prop() {
    return 'parent property';
  }
}

class Child extends Parent {
  constructor() {
    super();
  }
}

const child = new Child();
console.log(child.prop);
// ===========
