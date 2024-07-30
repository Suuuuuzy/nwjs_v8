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
// var gay = "fakeValue";

// // normally it will output undefined,
// // but if typeof (a === "string" && a == "fakeValue")
// // -> change a to an object: gay = { "fakeKey": "fakeValue", "fag": "fakeValue" }
// // this will output: fakeValue
// console.log(gay.fag); // recv type is string
// console.log(JSON.stringify(gay));

// // this will output: fakeValue
// // because it will check if gay has a fakeKey and the value is fakeValue
// // gay = { "fakeKey": "fakeValue", "fag": "fakeValue" }
// console.log(gay.cuck);
// console.log(JSON.stringify(gay));

// // this will output: fakeValue
// // because it will check if gay.fag is string "fakeValue"
// console.log(gay.fag.c);
// console.log(JSON.stringify(gay));

// var gay = "fakeValue";
// // step1: gay = { "fakeKey": "fakeValue", "les": "fakeValue" }
// // step2: gay = { "fakeKey": "fakeValue", "les": {"slut":"fakeValue", "fakeKey":"fakeValue"} }
// console.log(gay.les.slut);
// console.log(JSON.stringify(gay));

// this should output: {"fakeKey":"fakeValue","fag":"fakeValue"}
// no, because we don't really change gay, we change the return value of its property access instead
// console.log(JSON.stringify(gay));

// again the since a.fag is string and a.fag == "fakeValue", we change a.fag to an object
// now a = { "fakeKey": "fakeValue", "fag": "fakeValue" }
// this will output: fakeValue
// console.log(gay.fag.c);

// we can not do multiple layer in this way
var options = { 'fakeKey': 'fakeValue' };
// {'fakeKey': 'fakeValue', 'fag': 'fakeValue'};
console.log(options.fag); // recv type is object
console.log(options.fag.c);
console.log(options.slut); // recv type is object
console.log(JSON.stringify(options));
// drawback: we don't know if it's an array or number

// var a = wx.getStorageSync("wxapp");
// wx.request({
//     url: "https://api.weixin.qq.com/sns/jscode2session",
//     data: {
//         appid: a.args.app_id,
//         secret: a.args.app_secret,
//         js_code: o.code,
//         grant_type: "authorization_code"
//     },
//     method: "GET",
//     header: {
//         "content-type": "application/json"
//     },
//     success: function(o) {
//         t.deciyption(o.data.session_key, e.detail.encryptedData, e.detail.iv);
//     },
//     fail: function(e) {
//         console.log("err", e);
//     }
// });
// ==============
