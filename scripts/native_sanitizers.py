"""Fatal sanitizer policy shared by the standalone native harnesses."""

FLAGS = ["-fsanitize=address,undefined", "-fno-sanitize-recover=all",
         "-fno-omit-frame-pointer"]
