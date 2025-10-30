.. title:: clang-tidy - bugprone-unsafe-format-string

bugprone-unsafe-format-string
==============================

Detects usage of vulnerable format string functions with unbounded ``%s``
specifiers that can cause buffer overflows.

The check identifies calls to format string functions like ``sprintf``, ``scanf``,
and their variants that use ``%s`` format specifiers without field width limits.
This can lead to buffer overflow vulnerabilities when the input string is longer
than the destination buffer.

Examples
--------

.. code-block:: c

  char buffer[100];
  const char* input = "user input";
  
  // Unsafe: no field width limit
  sprintf(buffer, "%s", input);
  scanf("%s", buffer);
  
  // Safe: field width specified
  sprintf(buffer, "%.99s", input);
  scanf("%99s", buffer);
  
  // Safe alternative: use safer functions
  snprintf(buffer, sizeof(buffer), "%s", input);

Checked Functions
-----------------

The check detects unsafe format strings in these functions:

* ``sprintf``, ``vsprintf``
* ``scanf``, ``fscanf``, ``sscanf``
* ``vscanf``, ``vfscanf``, ``vsscanf``
* ``wscanf``, ``fwscanf``, ``swscanf``
* ``vwscanf``, ``vfwscanf``, ``vswscanf``

Recommendations
---------------

* Use ``snprintf`` instead of ``sprintf`` to prevent buffer overflows
* Add field width specifiers to ``%s`` format specifiers (e.g., ``%99s``)
* Consider using safer string handling functions when possible
