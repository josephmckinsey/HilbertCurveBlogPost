# filepath: /home/joseph/Programming/lean/HilbertCurveBlogPost/transform_dollars.py
import re
import sys


def transform_dollars(content):
    # Replace $$...$$ with $$`...`
    # Replace $...$ with $`...`

    # First handle double dollars ($$...$$) to avoid conflicts
    content = re.sub(r"\$\$([^$`]+)\$\$", r"$$`\1`", content)

    # Then handle single dollars ($...$) but avoid already transformed content
    content = re.sub(r"(?<!\$)\$([^$`]+)\$(?!\$)", r"$`\1`", content)

    return content


def test_transform_dollars():
    # Test basic single dollar cases
    assert transform_dollars("$x$") == "$`x`"
    assert transform_dollars("$x + y$") == "$`x + y`"

    # Test double dollar cases
    assert transform_dollars("$$x$$") == "$$`x`"
    assert transform_dollars("$$x + y$$") == "$$`x + y`"

    # Test mixed cases
    assert transform_dollars("Text $x$ and $$y$$ here") == "Text $`x` and $$`y` here"

    # Test idempotent cases - already transformed should remain unchanged
    assert transform_dollars("$`x`") == "$`x`"
    assert transform_dollars("$`x` hmm $$`y`") == "$`x` hmm $$`y`"
    assert transform_dollars("$$`x + y`") == "$$`x + y`"
    assert transform_dollars("Text $$`x` and $`y` here") == "Text $$`x` and $`y` here"

    # Test edge cases
    assert transform_dollars("") == ""
    assert transform_dollars("No math here") == "No math here"
    assert transform_dollars("$") == "$"
    assert transform_dollars("$$") == "$$"

    print("All tests passed!")


if __name__ == "__main__":
    # Read input from stdin (for VS Code selection)
    input_text = sys.stdin.read()
    print(transform_dollars(input_text))
