# Agda Tooling

This module contains custom utilities to automatize the following tasks in the `hott-intro` project (un-ticked features are not implemented yet):

- [x] **Solutions Index:** a markdown file listing all the exercises from the book that were solved
- [ ] **General Code Formatting:**
  - [ ] sort imports alphabetically, generate import groups, remove unused imports, etc.
  - [ ] rules for consistent indentation
  - [ ] detect unused values
- [ ] **Definition Browser:** Look up definitions in the code given a specific type

## Solutions Index

The `solutions-index` module generates a `SolutionsIndex.md` file inside the root `hott-intro` folder. 
This file lists all solutions to the exercises from the book that were implemented in **Agda**. Each item in the list references the specific line in the **Agda** code that contains the proof.

To identify the solutions, the tool expects a comment in the Agda code containing a string with the following format: `s"Exercise ${x_1}.${x_2}.${...}.${x_n}"`,
where each `x_i` is an alphanumeric string (e.g., "Exercise 4.3.a.ii"). It will then collect all these strings with their line number in source code, and generate a markdown list sorted by Exercise number.
