## Overview

This Python program uses the **PLY** (Python Lex-Yacc) library to verify if a given code snippet is written in **GCL** (Generalized Conditional Language). The program is designed to perform lexical analysis and syntactic parsing to ensure the code adheres to GCL syntax.

### How It Works

1. **Lexical Analysis**:
   - **Tokens**: The program defines various tokens such as identifiers, operators, and keywords using regular expressions.
   - **Lexer**: It tokenizes the input code, breaking it into meaningful components.

2. **Syntactic Parsing**:
   - **Grammar Rules**: The program specifies grammar rules to define the structure of valid GCL statements.
   - **Parser**: It analyzes the tokenized code to ensure it follows the defined syntax rules of GCL.

3. **Verification**:
   - The lexer and parser work together to validate the structure of the input code, confirming if it conforms to GCL.

### Example Usage

To run the program from the terminal, follow these steps:

1. **Prepare the Input Code**:
   Create a text file containing the GCL code you want to check, e.g., `input.gcl`.

3. **Run the Program**:
   Execute the Python script from the terminal, passing the input file as an argument. For example:

   ```bash
   python gcl.py input.gcl
