


var options = { 'fakeKey': 'fakeValue' };
Object.defineProperty(options, 'existingProperty', {
  enumerable: false
});
console.log(JSON.stringify(options));
console.log(options.a)
console.log(JSON.stringify(options));
console.log(options.a.fakeKey);
console.log(JSON.stringify(options));
console.log(options.a.b)
console.log(JSON.stringify(options));
// added_property: {'testkey': 'testvalue'}
// expect: options = { 'testkey': 'testvalue', 'a':{'testkey': 'testvalue'}};
// Object.defineProperty(options.a, 'fakekey', {
//   value: 'fakeValue',
//   enumerable: false, // This makes the property non-enumerable
//   configurable: true,
//   writable: true
// });
if (options.a.b.fakekey) {
  options.a.b.fakekey.__checkTaint__();
}
