const obj = {
  existingProperty: 'value'
};

// Set the existing property to be non-enumerable
Object.defineProperty(obj, 'existingProperty', {
  enumerable: false
});
