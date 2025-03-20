import yaml
import os
from pathlib import Path

def load_config(config_path=None):
    """
    Load configuration from a YAML file.

    Args:
        config_path: Path to the config file. If None, looks for config.yaml in the current directory.

    Returns:
        Dictionary containing configuration values.
    """
    if config_path is None:
        config_path = Path(__file__).parent / 'config.yaml'

    if not os.path.exists(config_path):
        raise FileNotFoundError(f"Config file not found at {config_path}. Please create one based on config.template.yaml.")

    with open(config_path, 'r') as file:
        config = yaml.safe_load(file)

    return config

def get_api_key(provider, config=None):
    """
    Get API key for a specific provider.

    Args:
        provider: The provider name (e.g., 'openai', 'anthropic')
        config: Optional pre-loaded config. If None, loads from default location.

    Returns:
        API key string or empty string if not found
    """
    if config is None:
        try:
            config = load_config()
        except FileNotFoundError:
            return ""

    # Try to get from config
    api_keys = config.get('api_keys', {})
    return api_keys.get(provider, "")