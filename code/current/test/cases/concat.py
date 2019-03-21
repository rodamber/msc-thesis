from src.synthesis.smt.lines.types import Example
import pyrsistent as p

cases = (
    # Size 2
    (
        Example(inputs=p.v('John', 'Doe'), output='John Doe'), ),

    # Size 2
    (Example(inputs=p.v('John', 'Doe'), output='John Doe'),
     Example(inputs=p.v('Anne', 'Smith'), output='Anne Smith')),

    # Size 3
    (Example(inputs=p.v('John', 'Doe', '-Odoi'), output='John Doe-Odoi'),
     Example(
         inputs=p.v('Anne', 'Smith', '-Sonian'), output='Anne Smith-Sonian')),

    # Size 3, learning the prefix
    (Example(inputs=p.v('John', 'Doe'), output='Dr. John Doe'),
     Example(inputs=p.v('Anne', 'Smith'), output='Dr. Anne Smith')),

    # Size 3, same as before
    (Example(inputs=p.v('John', 'Doe'), output='Dr. John Doe'),
     Example(inputs=p.v('Anne', 'Smith'), output='Dr. Anne Smith')),

    # Size 4
    (Example(inputs=p.v('John', 'Michael', 'Doe'), output='John Michael Doe'),
     Example(inputs=p.v('Anne', 'Marie', 'Smith'), output='Anne Marie Smith')),

    # Size 5, learning the prefix
    (Example(
        inputs=p.v('John', 'Michael', 'Doe'), output='Dr. John Michael Doe'),
     Example(
         inputs=p.v('Anne', 'Marie', 'Smith'), output='Dr. Anne Marie Smith')),

    # Size 6
    (Example(
        inputs=p.v('John', 'Oliver', 'Michael', 'Doe'),
        output='John Oliver Michael Doe'),
     Example(
         inputs=p.v('Anne', 'Emily', 'Marie', 'Smith'),
         output='Anne Emily Marie Smith')),
)
